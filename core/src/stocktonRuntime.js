var _ = require("lodash");
var util = require('util');
var LL = require('./baseLLParser');
var 	Log4js = require('log4js');

var logger = Log4js.getLogger('stocktonRuntime');
var debug = true;
function PredictionContext(cachedHashCode){
	this.cachedHashCode = cachedHashCode;
}

PredictionContext.fromRuleContext = function(atn, outerContext){
	if(outerContext == null)
		outerContext = 'EMPTY';
	if(outerContext.parent==null || outerContext == 'EMPTY')
		return 'EMPTY';
	var parent = PredictionContext.fromRuleContext(atn, outerContext.parent);
	var state = atn.states[outerContext.invokingState];
	var transition = state.transitions[0];
	return new SingletonPredictionContext(parent, transition.followState.stateNumber);
};

PredictionContext.merge = function(){
	//todo
};

PredictionContext.EMPTY_RETURN_STATE = Number.MAX_VALUE;
PredictionContext.prototype = {
	EMPTY_RETURN_STATE: PredictionContext.EMPTY_RETURN_STATE,

	isEmpty:function(){
		return this == PredictionContext.EMPTY;
	},
	toString:function(){
		return this.cachedHashCode;
	},
	calculateHashCode:function(parent, returnState){
		return JSON.stringify({
			p:parent.toString(),
			r:returnState
		});
	},
	calculateEmptyHashCode:function(){
		return '';
	},
	
	hasEmptyPath:function(){
		return this.getReturnState(this.size() - 1) == this.EMPTY_RETURN_STATE;
	}
};

function SingletonPredictionContext(parent, returnState){
	PredictionContext.call(this, 
		parent != null? this.calculateHashCode(parent, returnState) : this.calculateEmptyHashCode());
	if(returnState == -1) throw new Error('Invalid state number');
	this.parent = parent;
	this.returnState = returnState;
}

SingletonPredictionContext.create = function(parent, returnState){
	if ( returnState == this.EMPTY_RETURN_STATE && parent == null ) {
		// someone can pass in the bits of an array ctx that mean $
		return PredictionContext.EMPTY;
	}
	return new SingletonPredictionContext(parent, returnState);
};

SingletonPredictionContext.prototype = _.create(PredictionContext.prototype, {

	size:function(){
		return 1;
	},
	getReturnState:function(){
		return this.returnState;
	},
	getParent:function(index){
		return this.parent;
	}
});

function EmptyPredictionContext(){
	SingletonPredictionContext.call(this, null, this.EMPTY_RETURN_STATE);
}
EmptyPredictionContext.prototype = _.create(SingletonPredictionContext.prototype,{
		isEmpty:function(){ return true; },
		size:function() {
			return 1;
		},
		getReturnState:function(index){
			this.returnState;
		}
});
PredictionContext.EMPTY = new EmptyPredictionContext();
	
function ATNConfig(state, alt, context, semanticContext){
	if(semanticContext === undefined)
		this.semanticContext = SemanticContext.NONE;
	this.state = state;
	this.alt = alt;
	this.context = context;
	this._key = JSON.stringify({
			s:this.state.stateNumber,
			a:this.alt,
			c:this.context == null? null: this.context.toString(),
			m:this.semanticContext.toString()
	});
}
ATNConfig.prototype.toString = function(){
	return this._key;
}

_DECISION_STATE = {
	basicBlockStart: true, plusBlockStart:true, starBlockStart:true,
	plusLoopback:true, starLoopEntry:true, tokensStart:true
};

function isDecisionState(state){
	return _.has(_DECISION_STATE, state.type);
}

function LexerATNConfig(obj){
	if(obj.config)
		this.initWithConfig(obj.config);
	delete obj.config;
	
	_.extend(this, obj);
	this.passedThroughNonGreedyDecision = this.checkNonGreedyDecision(
		this.checkNonGreedyDecision, this.state);
	this._key = JSON.stringify({
			s:this.state.stateNumber,
			a:this.alt,
			c:this.context == null? null: this.context.toString(),
			m:this.semanticContext.toString(),
			p:this.passedThroughNonGreedyDecision ? 1 : 0,
			l:this.lexerActionExecutor? this.lexerActionExecutor.toString() : null
	});
}

LexerATNConfig.prototype = _.create(ATNConfig.prototype, {
		initWithConfig: function(config){
			this.alt = config.alt;
			this.semanticContext = config.semanticContext;
			this.reachesIntoOuterContext = config.reachesIntoOuterContext;
			this.lexerActionExecutor = config.lexerActionExecutor;
			this.passedThroughNonGreedyDecision = config.passedThroughNonGreedyDecision;
		},
		
		checkNonGreedyDecision:function(checkNonGreedyDecision, target){
			return checkNonGreedyDecision || isDecisionState(target);
			// we only support nonGreedy
		}
});

var SemanticContext = {};

SemanticContext.Predicate = function(){
	this.ruleIndex = -1;
    this.predIndex = -1;
    this.isCtxDependent = false;
    this._key = JSON.stringify({
    		r:this.ruleIndex,
    		p:this.predIndex,
    		c: this.isCtxDependent? 1: 0
    });
}

SemanticContext.Predicate.prototype = {
	toString:function(){
		return this._key;
	}
};

SemanticContext.NONE = new SemanticContext.Predicate();

function DFAState(configs){
	this.stateNumber = -1;
	this.isAcceptState = false;
	this.prediction = 0;
	//other memebers
	// configs
	// edges
	// requiresFullContext
	// predicates
	// lexerActionExecutor
	this.configs = configs;
}

DFAState.prototype ={
	toString:function(){
		return this.configs.toString();
	}
};

function ConfigHashSet(){
	
}


function ATNConfigSet(){
	this.configs = [];
	this.hasSemanticContext = false;
	this.readonly = false;
	this.fullCtx = true;
	this.cachedHashCode = -1;
	//this.configLookup = null;
}

ATNConfigSet.prototype = {
	add:function(config, mergeCache){
		if ( this.readonly ) throw new Error("This set is readonly");
		if ( config.semanticContext!=SemanticContext.NONE ) {
			this.hasSemanticContext = true;
		}
		if (config.reachesIntoOuterContext > 0) {
			this.dipsIntoOuterContext = true;
		}
		if(!this.configLookup.hasOwnProperty(config)){
			this.cachedHashCode = -1;
			this.configs.push(config);  // track order here
			return true;
		}
		var existing = this.configLookup[config];
		// a previous (s,i,pi,_), merge with it and save result
		var rootIsWildcard = !this.fullCtx;
		var merged =
			PredictionContext.merge(existing.context, config.context, rootIsWildcard, mergeCache);
		// no need to check for existing.context, config.context in cache
		// since only way to create new graphs is "call rule" and here. We
		// cache at both places.
		existing.reachesIntoOuterContext =
			Math.max(existing.reachesIntoOuterContext, config.reachesIntoOuterContext);
		existing.context = merged; // replace context; no need to alt mapping
		return true;
	},
	
	setReadonly:function(b){
		this.readonly = b;
		delete this.configLookup;
	},
	
	toString:function(){
		if(this.readonly){
			if (this.cachedHashCode === -1) {
				this.cachedHashCode = this.configs.join();
			}

			return this.cachedHashCode;
		}
		return this.configs.join();
	},
	isEmpty: function(){
		return this.configs.length === 0;
	}
};

//@finished
function OrderedATNConfigSet(){
	ATNConfigSet.call(this);
	this.configLookup = {};
}
OrderedATNConfigSet.prototype = _.create(ATNConfigSet.prototype);

function ATNSimulator(atn, sharedContextCache){
	this.atn = atn;
	this.sharedContextCache = sharedContextCache;
}

ATNSimulator.ERROR = new DFAState(new ATNConfigSet());
ATNSimulator.ERROR.stateNumber = Number.MAX_VALUE;

ATNSimulator.prototype ={
	ERROR: ATNSimulator.ERROR
};

function SimState(){
	this.reset();
}
SimState.prototype ={
	reset:function(){
		this.index = -1;
		this.line = 0;
		this.charPos = -1;
		this.dfaState = null;
	}
};

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
			this.logger.debug("matchATN() mode %d start: %s\n", this.mode, startState);
		}
		var old_mode = this.mode;
		var s0_closure = this.computeStartState(input, startState);
		var suppressEdge = s0_closure.hasSemanticContext;
		s0_closure.hasSemanticContext = false;
		var next = this.addDFAState(s0_closure);
		if (!suppressEdge) {
			this.decisionToDFA[this.mode].s0 = next;
		}
		this.logger.debug('suppressEdge: %j, s0 = %s\ns0_closure = %s', suppressEdge, next+'', s0_closure.toString());
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
		while ( true ) { // while more work
			if ( debug ) {
				this.logger.debug("execATN() execATN loop starting closure: %s\n", s.configs);
			}
			var target = this.getExistingTargetState(s, t);
			if (target == null) {
				target = this.computeTargetState(input, s, t);
			}
			
			if (target == this.ERROR) {
				break;
			}
			
			if (target.isAcceptState) {
				/** todo */this.captureSimState(this.prevAccept, input, target);
				if (t == LL.Lexer.prototype.EOF) {
					break;
				}
			}

			if (t != LL.Lexer.prototype.EOF) {
				/** todo */this.consume(input);
				t = input.la(1);
			}
			s = target;
		}
		return this.failOrAccept(this.prevAccept, input, s.configs, t);
	},
	
	failOrAccept: function(prevAccept, input, reach, t){
		if (prevAccept.dfaState != null) {
			var lexerActionExecutor = prevAccept.dfaState.lexerActionExecutor;
			/* todo */this.accept(input, lexerActionExecutor, this.startIndex,
				prevAccept.index, prevAccept.line, prevAccept.charPos);
			return prevAccept.dfaState.prediction;
		}
		else {
			// if no accept and EOF is first char, return EOF
			if ( t==LL.Lexer.prototype.EOF && input.offset == startIndex ) {
				return LL.Lexer.prototype.EOF;
			}

			throw _LexerNoViableAltException(this.recog, input, this.startIndex, reach);
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
			var c = new LexerATNConfig({
				state:target, alt: i+1, context:initialContext,
				semanticContext: SemanticContext.NONE,
				passedThroughNonGreedyDecision: false
			});
			this.closure(input, c, configs, false, false);
		}
		return configs;
	},
	
	computeTargetState:function(input, s, t){
		var reach = new OrderedATNConfigSet();

		// if we don't find an existing DFA state
		// Fill reach starting from closure, following t transitions
		this.getReachableConfigSet(input, s.configs, reach, t);

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
	
	// there is another overwriten addDFAEdge()
	addDFAEdge: function(p, t, q){
		if(q instanceof ATNConfigSet){
			var suppressEdge = q.hasSemanticContext;
			q.hasSemanticContext = false;
			var to = this._addDFAState(q);
			return to;
		}
		if (t < this.MIN_DFA_EDGE || t > this.MAX_DFA_EDGE) {
			// Only track edges within the DFA bounds
			return;
		}
		if ( debug ) {
			this.logger.debug("EDGE "+p+" -> "+q+" upon "+ t );
		}
		if ( p.edges==null ) {
			//  make room for tokens 1..n and -1 masquerading as index 0
			p.edges = new Array(this.MAX_DFA_EDGE - this.MIN_DFA_EDGE +1);
		}
		p.edges[t - this.MIN_DFA_EDGE] = q; // connect
	},
	
	_addDFAState:function(configs){
		if(configs.hasSemanticContext)
			throw new Error('failed to assert !configs.hasSemanticContext');
		var proposed = new DFAState(configs);
		var firstConfigWithRuleStopState = null;
		configs.some(function(c){
			if ( c.state.type === 'ruleStop' )	{
				firstConfigWithRuleStopState = c;
				return true;
			}
			return false;
		});

		if ( firstConfigWithRuleStopState!=null ) {
			proposed.isAcceptState = true;
			proposed.lexerActionExecutor = firstConfigWithRuleStopState.lexerActionExecutor;
			proposed.prediction = this.atn.ruleToTokenType[firstConfigWithRuleStopState.state.ruleName];
		}

		var dfa = this.decisionToDFA[this.mode];
		//synchronized (dfa.states) {
			existing = dfa.states[proposed.toString()];
			if ( existing!=null ) return existing;

			var newState = proposed;

			newState.stateNumber = _.size(dfa.states);
			configs.setReadonly(true);
			newState.configs = configs;
			dfa.states[newState.toString()] = newState;
			return newState;
		//}
	},
	
	getReachableConfigSet:function(input, closure, reach, t){
		var skipAlt = 0;
		_.each(closure.configs, function(c){
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

					if (this.closure(input, new LexerATNConfig(c, target, lexerActionExecutor), reach, currentAltReachedAcceptState, true)) {
						// any remaining configs for this alt have a lower priority than
						// the one that just reached an accept state.
						skipAlt = c.alt;
						break;
					}
				}
			}
		});
	},
	
	getReachableTarget:function(trans, t){
		if (trans.matches(t, Character.MIN_VALUE, Character.MAX_VALUE)) {
			return trans.target;
		}

		return null;
	},
	
	addDFAState:function(configs){
		if(configs.hasSemanticContext)
			throw new Error('configs.hasSemanticContext can\'t be true in here');
		var proposed = new DFAState(configs);
		var firstConfigWithRuleStopState = null;
		_.some(configs.configs, function(c){
				if(c.state.type == 'ruleStop'){
					firstConfigWithRuleStopState = c;
					return true;
				}
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
		this.logger.debug('addDFAState() newState = %s', newState);
		return newState;
	},
	/**
	@param input baseLLParser's lex object
	*/
	closure:function(input, config, configs, currentAltReachedAcceptState, speculative){
		if ( debug ) {
			this.logger.debug("closure("+config.toString()+")");
		}
		if ( config.state.type == 'ruleStop' ) {
			if(debug)
				this.logger.debug("closure at %s rule stop %s\n", config.state.ruleName, config);
			if ( config.context == null || config.context.hasEmptyPath() ) {
				if (config.context == null || config.context.isEmpty()) {
					configs.add(config);
					return true;
				}
				else {
					configs.add(new LexerATNConfig({
						config: config,
						state: config.state,
						context:PredictionContext.EMPTY
					}));
					currentAltReachedAcceptState = true;
				}
			}
			if ( config.context!=null && !config.context.isEmpty() ) {
				for (var i = 0, l= config.context.size(); i < l; i++) {
					if (config.context.getReturnState(i) != PredictionContext.EMPTY_RETURN_STATE) {
						var newContext = config.context.getParent(i); // "pop" return state
						var returnState = this.atn.states.get(config.context.getReturnState(i));
						var c = new LexerATNConfig({
								state: returnState,
								alt: config.alt,
								context:newContext,
								semanticContext: SemanticContext.NONE,
								passedThroughNonGreedyDecision: false
						});
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
		for (var i=0, l= p.transitions.length; i< l; i++) {
			var t = p.transitions[i];
			var c = this.getEpsilonTarget(input, config, t, configs, speculative);
			if ( c!=null ) {
				currentAltReachedAcceptState = this.closure(input, c, configs, currentAltReachedAcceptState, speculative);
			}
		}

		return currentAltReachedAcceptState;
	},
	
	getEpsilonTarget:function(input, config, t, configs, speculative){
		c = null;
		switch (t.type) {
			case 'rule':
				var newContext =
						SingletonPredictionContext.create(config.context, t.followState.stateNumber);
					c = new LexerATNConfig({config: config, state:t.target, context: newContext});
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
					c = new LexerATNConfig({config: config, state:t.target});
				}
				break;
			case 'action':
				if (config.context == null || config.context.hasEmptyPath()) {
					// execute actions anywhere in the start rule for a token.
					//todo
					var lexerActionExecutor = LexerActionExecutor.append(config.lexerActionExecutor, t.actionContent);
					c = new LexerATNConfig({config: config, state: t.target, lexerActionExecutor:lexerActionExecutor});
					break;
				}else {
					// ignore actions in referenced rules
					c = new LexerATNConfig({config: config, state: t.target});
					break;
				}
			case 'epsilon':
				c = new LexerATNConfig({config: config, state:t.target});
				break;
		}
	},
	
	evaluatePredicate:function(input, ruleName, predContent, speculative){
		//todo
		this.logger.debug('evaluatePredicate() --> %s', predContent);
		return true;
	}
});

var RETURN_FALSE = function(){
		return false;
	};
	
var TransitionMatches = {
	precedence: RETURN_FALSE,
	predicate: RETURN_FALSE,
	epsilon: RETURN_FALSE,
	action: RETURN_FALSE,
	atom:function(tran, symbol){
		return trans.label == symbol;
	},
	range:function(tran, symbol, minVocabSymbol, maxVocabSymbol) {
		return symbol >= tran.from && symbol <= tran.to;
	},
	rule: RETURN_FALSE,
	
	set:function(tran, symbol){
		return tran.set.contains(symbol);
	},
	
	notSet:function(tran, symbol, minVocabSymbol, maxVocabSymbol){
		return symbol >= minVocabSymbol && symbol <= maxVocabSymbol &&
			!TransitionMatches.set(tran, symbol, minVocabSymbol, maxVocabSymbol);
	},
	
	wildcard:function(tran, symbol, minVocabSymbol, maxVocabSymbol){
		return symbol >= minVocabSymbol && symbol <= maxVocabSymbol;
	}
};

Transition = {
	matches:function(tran, moreArgs){
		return TransitionMatches[tran.type].apply(tran, _.toArray(arguments).slice(1));
	}
};

function DFA(json){
	_.extend(this, json);
	this.states = {};
}

function generateLexer(atn){
	var _decisionToDFA = [], i = 0;
	atn.decisionToState.forEach(function(s){
		_decisionToDFA.push(new DFA({atnStartState: s, decision: i}));
	});
	var _interp = new LexerATNSimulator(atn, _decisionToDFA, null);
	return function nextToken(lex, c){
		var type = _interp.match(this, 0);
	}
}

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

module.exports = {
	ATNConfig: ATNConfig,
	PredictionContext: PredictionContext,
	SingletonPredictionContext: SingletonPredictionContext,
	EmptyPredictionContext: EmptyPredictionContext,
	generateLexer:generateLexer,
	DFA: DFA,
	LexerATNSimulator: LexerATNSimulator
};
