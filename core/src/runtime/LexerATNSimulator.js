var Transition = require('./Transition'),
     _ = require("lodash"),
    util = require('util'),
    Log4js = require('log4js'),
    IntervalSet = require('..//misc.js').IntervalSet;

var runtimeMisc = require('./runtime-misc');


var debug = true;

function LexerATNSimulator(atn, decisionToDFA, sharedContextCache){
    ATNSimulator.call(this, atn, sharedContextCache);
    this.recog = null;
    this.mode = 0;//todo
    this.decisionToDFA = decisionToDFA;
    this.startIndex = -1;
    this.line = 1;
    this.charPositionInLine = 0;
    this.match_calls = 0;
    this.prevAccept = new SimState();
}

LexerATNSimulator.prototype = _.create(ATNSimulator.prototype, {

    MIN_DFA_EDGE: 0,
    MAX_DFA_EDGE: 127,
    logger: Log4js.getLogger('LexerATNSimulator'),

    match:function(input, mode){
        if(mode === undefined)
            mode = 0;
        this.mode = mode;
        this.match_calls++;
        try{
            this.startIndex = input.offset;
            this.prevAccept.reset();
            var dfa = this.decisionToDFA[mode];
            if ( dfa.s0==null ) {
                return this.matchATN(input);
            }
            else {
                return this.execATN(input, dfa.s0);
            }
        }finally{
            // todo input.release(mark);
        }
    },

    matchATN:function(input){
        var startState = this.atn.states[this.mode];
        if ( debug ) {
            this.logger.debug("matchATN() mode %d start: %s\n", this.mode, util.inspect(startState));
        }
        var old_mode = this.mode;
        var s0_closure = this.computeStartState(input, startState);
        var suppressEdge = s0_closure.hasSemanticContext;
        s0_closure.hasSemanticContext = false;
        var next = this.addDFAState(s0_closure);
        if (!suppressEdge) {
            this.decisionToDFA[this.mode].s0 = next;
        }
        this.logger.debug('matchATN() suppressEdge: %j, s0 = %s\ns0_closure = %s', suppressEdge, next+'', s0_closure.toString());
        var predict = this.execATN(input, next);

        if ( debug ) {
            this.logger.debug( "matchATN() DFA after matchATN: %s\n", this.decisionToDFA[old_mode]);
        }

        return predict;
    },

    execATN: function(input, ds0){
        if ( debug ) {
            this.logger.debug("execATN() start state closure=%s\n", ds0.configs);
        }
        var t = input.la(1);
        var s = ds0; // s is current/from DFA state
        var EOF = LL.Lexer.prototype.EOF;
        while ( true ) { // while more work
            if ( debug ) {
                this.logger.debug("execATN() execATN loop starting closure: %s\n", s.configs);
            }
            var target = this.getExistingTargetState(s, t);
            if (target == null) {
                target = this.computeTargetState(input, s, t);
            }
            if (target === this.ERROR) {
                break;
            }
            this.logger.debug('3. no ERROR target.isAcceptState:' + target.isAcceptState);
            if (target.isAcceptState) {
                this.captureSimState(this.prevAccept, input, target);
                if (t === EOF) {
                    break;
                }
            }

            if (t !== EOF) {
                this.consume(input);
                t = input.la(1);
                this.logger.debug('execATN() next input '+ t);
            }
            s = target;
        }
        return this.failOrAccept(this.prevAccept, input, s.configs, t);
    },

    failOrAccept: function(prevAccept, input, reach, t){
        if (prevAccept.dfaState != null) {
            var lexerActionExecutor = prevAccept.dfaState.lexerActionExecutor;
            this.accept(input, lexerActionExecutor, this.startIndex,
                prevAccept.index, prevAccept.line, prevAccept.charPos);
            return prevAccept.dfaState.prediction;
        }
        else {
            // if no accept and EOF is first char, return EOF
            if ( t === LL.Lexer.prototype.EOF && input.offset === this.startIndex ) {
                return LL.Lexer.prototype.EOF;
            }

            throw _LexerNoViableAltException(this.recog, input, this.startIndex, reach);
        }
    },

    accept:function(input, lexerActionExecutor, startIndex, index, line, charPos) {
        if ( debug ) {
            this.logger.debug('ACTION %s\n', lexerActionExecutor);
        }

        // seek to after last char in token
        //input.seek(index);
        input.offset = index;
        this.line = line;
        this.charPositionInLine = charPos;
        if (input.la(1) !== EOF) {
            this.consume(input);
        }

        if (lexerActionExecutor != null && this.recog != null) {
            lexerActionExecutor.execute(this.recog, input, startIndex);
        }

    },

    getExistingTargetState:function(s, t){
        if (s.edges == null || t < this.MIN_DFA_EDGE || t > this.MAX_DFA_EDGE) {
            return null;
        }

        var target = s.edges[t - this.MIN_DFA_EDGE];
        if (debug && target != null) {
            this.logger.debug("getExistingTargetState() "+s.stateNumber+
                " edge to "+target.stateNumber);
        }

        return target;
    },
    /**
     @param p ATNState
     */
    computeStartState:function(input, p){
        var initialContext = PredictionContext.EMPTY;
        var configs = new OrderedATNConfigSet();
        for (var i=0, l=p.transitions.length; i< l; i++) {
            var target = p.transitions[i].target;
            var c = new LexerATNConfig(target, i+1, initialContext);
            this.closure(input, c, configs, false, false);
        }
        return configs;
    },

    computeTargetState:function(input, s, t){
        var reach = new OrderedATNConfigSet();
        // if we don't find an existing DFA state
        // Fill reach starting from closure, following t transitions
        this.getReachableConfigSet(input, s.configs, reach, t);
        this.logger.debug('computeTargetState() reach is empty? '+ reach.isEmpty()+
            ', s=' + s+ ', t='+ t
        );

        if ( reach.isEmpty() ) { // we got nowhere on t from s
            if (!reach.hasSemanticContext) {
                // we got nowhere on t, don't throw out this knowledge; it'd
                // cause a failover from DFA later.
                this.addDFAEdge(s, t, this.ERROR);
            }

            // stop when we can't match any more char
            return this.ERROR;
        }

        // Add an edge from s to target DFA found/created for reach

        return this.addDFAEdge(s, t, reach);
    },

    /** there is another overwriten addDFAEdge()
     @return DFAState
     */
    addDFAEdge: function(p, t, q){
        if(q instanceof ATNConfigSet){
            var suppressEdge = q.hasSemanticContext;
            q.hasSemanticContext = false;
            var to = this.addDFAState(q);
            return to;
        }
        if (t < this.MIN_DFA_EDGE || t > this.MAX_DFA_EDGE) {
            // Only track edges within the DFA bounds
            return;
        }
        if ( debug ) {
            this.logger.debug("addDFAEdge() EDGE "+p+" -> "+q+" upon "+ t );
        }
        if ( p.edges==null ) {
            //  make room for tokens 1..n and -1 masquerading as index 0
            p.edges = new Array(this.MAX_DFA_EDGE - this.MIN_DFA_EDGE +1);
        }
        p.edges[t - this.MIN_DFA_EDGE] = q; // connect
    },


    getReachableConfigSet:function(input, closure, reach, t){
        var skipAlt = 0;
        closure.configs.forEach(function(c){
            var currentAltReachedAcceptState = c.alt == skipAlt;
            if (currentAltReachedAcceptState && c.passedThroughNonGreedyDecision) {
                return;
            }

            if(debug)
                this.logger.debug('getReachableConfigSet() testing %s at %s\n', t, c.toString());
            var n = c.state.transitions.length;
            for (var ti=0; ti<n; ti++) {
                var trans = c.state.transitions[ti];

                var target = this.getReachableTarget(trans, t);
                if ( target!=null ) {
                    var lexerActionExecutor = c.lexerActionExecutor;
                    if (lexerActionExecutor != null) {
                        lexerActionExecutor = lexerActionExecutor.fixOffsetBeforeMatch(input.offset - this.startIndex);
                    }
                    if (this.closure(input,
                            new LexerATNConfig(c, target, lexerActionExecutor),
                            reach, currentAltReachedAcceptState, true)) {
                        // any remaining configs for this alt have a lower priority than
                        // the one that just reached an accept state.
                        skipAlt = c.alt;
                        break;
                    }
                }
            }
        }, this);
    },

    getReachableTarget:function(trans, t){
        if (Transition.matches(trans, t, 0, 0xffff)) {
            return trans.target;
        }

        return null;
    },



    addDFAState:function(configs){
        this.logger.debug('addDFAState() configs = %s', util.inspect(configs));
        if(configs.hasSemanticContext)
            throw new Error('configs.hasSemanticContext can\'t be true in here');
        var proposed = new DFAState(configs);
        var firstConfigWithRuleStopState = null;

        configs.configs.some( function(c){
            if(c.state.type === 'ruleStop'){
                firstConfigWithRuleStopState = c;
                return true;
            }
            return false;
        });
        if ( firstConfigWithRuleStopState ){
            proposed.isAcceptState = true;
            proposed.lexerActionExecutor = firstConfigWithRuleStopState.lexerActionExecutor;
            proposed.prediction = this.atn.ruleToTokenType[firstConfigWithRuleStopState.state.ruleName];
        }
        var dfa = this.decisionToDFA[this.mode];
        var existing = dfa.states[proposed];
        if ( existing!=null ) return existing;

        var newState = proposed;

        newState.stateNumber = _.size(dfa.states);
        configs.setReadonly(true);
        newState.configs = configs;
        dfa.states[newState] = newState;
        this.logger.debug('addDFAState() newState = %s', util.inspect(newState));
        return newState;
    },
    /**
     @param input baseLLParser's lex object
     */
    closure:function(input, config, configs, currentAltReachedAcceptState, speculative){
        if ( debug ) {
            this.logger.debug("closure("+config.toString()+")");
        }
        if ( config.state.type === 'ruleStop' ) {
            if(debug)
                this.logger.debug("closure at %s rule stop %s\n", config.state.ruleName, config);
            if ( config.context == null || config.context.hasEmptyPath() ) {
                if (config.context == null || config.context.isEmpty()) {
                    configs.add(config);
                    return true;
                }
                else {
                    configs.add(new LexerATNConfig(config, config.state, PredictionContext.EMPTY));
                    currentAltReachedAcceptState = true;
                }
            }

            if ( config.context!=null && !config.context.isEmpty() ) {
                for (var i = 0, l= config.context.size(); i < l; i++) {

                    if (config.context.getReturnState(i) != PredictionContext.EMPTY_RETURN_STATE) {

                        var newContext = config.context.getParent(i); // "pop" return state
                        var returnState = this.atn.states[config.context.getReturnState(i)];
                        var c = new LexerATNConfig(returnState, config.alt, newContext);
                        currentAltReachedAcceptState = this.closure(input, c, configs, currentAltReachedAcceptState, speculative);
                    }
                }
            }

            return currentAltReachedAcceptState;
        }

        // optimization
        if ( !config.state.epsilonOnlyTransitions ) {
            if (!currentAltReachedAcceptState || !config.passedThroughNonGreedyDecision) {
                configs.add(config);
            }
        }

        var p = config.state;
        this.logger.debug('transitions '+ p.transitions.length);
        for (var i=0, l= p.transitions.length; i< l; i++) {

            var t = p.transitions[i];
            var c = this.getEpsilonTarget(input, config, t, configs, speculative);
            this.logger.debug('transition '+ i+ ' getEpsilonTarget '+ c);
            if ( c!=null ) {
                currentAltReachedAcceptState = this.closure(input, c, configs, currentAltReachedAcceptState, speculative);
            }
        }

        return currentAltReachedAcceptState;
    },

    getEpsilonTarget:function(input, config, t, configs, speculative){
        var c = null;
        switch (t.type) {
            case 'rule':
                var newContext =
                    SingletonPredictionContext.create(config.context, t.followState.stateNumber);
                c = new LexerATNConfig(config, t.target, newContext);
                break;
            case 'precedence':
                throw new Error("Precedence predicates are not supported in lexers.");
            case 'predicate':
                /*  Track traversing semantic predicates. If we traverse,
                 we cannot add a DFA state for this "reach" computation
                 because the DFA would not test the predicate again in the
                 future. Rather than creating collections of semantic predicates
                 like v3 and testing them on prediction, v4 will test them on the
                 fly all the time using the ATN not the DFA. This is slower but
                 semantically it's not used that often. One of the key elements to
                 this predicate mechanism is not adding DFA states that see
                 predicates immediately afterwards in the ATN. For example,

                 a : ID {p1}? | ID {p2}? ;

                 should create the start state for rule 'a' (to save start state
                 competition), but should not create target of ID state. The
                 collection of ATN states the following ID references includes
                 states reached by traversing predicates. Since this is when we
                 test them, we cannot cash the DFA state target of ID.
                 */
                var pt = t;
                if ( debug ) {
                    this.logger.debug("EVAL rule "+pt.ruleName+":"+pt.predIndex);
                }
                configs.hasSemanticContext = true;
                if (this.evaluatePredicate(input, pt.ruleIndex, pt.predContent, speculative)) {
                    c = new LexerATNConfig(config, t.target);
                }
                break;
            case 'action':
                if (config.context == null || config.context.hasEmptyPath()) {
                    // execute actions anywhere in the start rule for a token.
                    //todo
                    var lexerActionExecutor = LexerActionExecutor.append(config.lexerActionExecutor, t.actionContent);
                    c = new LexerATNConfig(config, t.target, lexerActionExecutor);
                    break;
                }else {
                    // ignore actions in referenced rules
                    c = new LexerATNConfig(config, t.target);
                    break;
                }
            case 'epsilon':
                c = new LexerATNConfig(config, t.target);
                break;
        }

        return c;
    },

    evaluatePredicate:function(input, ruleName, predContent, speculative){
        //todo
        this.logger.debug('evaluatePredicate() --> %s', predContent);
        return true;
    },

    consume:function(input) {
        var curChar = input.la(1);
        if ( curChar==='\n' ) {
            line++;
            this.charPositionInLine=0;
        } else {
            this.charPositionInLine++;
        }
        input.consume();
    },

    captureSimState:function(settings, input, dfaState) {
        settings.index = input.offset;
        settings.line = this.line;
        settings.charPos = this.charPositionInLine;
        settings.dfaState = dfaState;
    }
});

function _LexerNoViableAltException(lexer, input, startIndex, deadEndConfigs){
    var e = new Error('LexerNoViableAlt');
    e.recognizer = lexer;
    e.input = input;
    e.ctx = null;
    e.startIndex = startIndex;
    e.deadEndConfigs = deadEndConfigs;
    console.log('startIndex: '+ e.startIndex);
    return e;
}