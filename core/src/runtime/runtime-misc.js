//'use strict';

var _ = require("lodash"),
    util = require('util'),
    Log4js = require('log4js'),
    sutil = require('./stockton-util'),
    IntervalSet = require('./misc.js').IntervalSet,
    Transition = require('./Transition');

var logger = Log4js.getLogger('stocktonRuntime');

function ATNConfig(){
    if(arguments.length === 1 && arguments[0] instanceof ATNConfig) {
        this._init1.apply(this, arguments);
    }else if(arguments[0] instanceof ATNConfig){
        if(arguments.length === 2) {
            if (arguments[1] instanceof SemanticContext)
                this._init6.apply(this, arguments);
            else
                this._init4.apply(this, arguments);
        }else if(arguments.length === 3) {
            if (arguments[2] instanceof SemanticContext) {
                this._init5.apply(this, arguments);
            } else if (arguments[2] instanceof PredictionContext) {
                this._init7.apply(this, arguments);
            } else
                throw new Error('invalid ATNConfig constructor');

        }else if(arguments.length === 4){
            this._init8.apply(this, arguments);
        }
    }else{
        this._init23.apply(this, arguments);
    }
    this._key = JSON.stringify({
        s:this.state.stateNumber,
        a:this.alt,
        c:this.context == null? null: this.context.toString(),
        m:this.semanticContext.toString()
    });
}

ATNConfig.prototype = {
    _init1: function(old) {
        this.state = old.state;
        this.alt = old.alt;
        this.context = old.context;
        this.semanticContext = old.semanticContext;
        this.reachesIntoOuterContext = old.reachesIntoOuterContext;
    },

    _init23: function(state, alt, context, semanticContext) {
        this.state = state;
        this.alt = alt;
        this.context = context;
        if(semanticContext === undefined)
            semanticContext = SemanticContext.NONE;
        this.semanticContext = semanticContext;
    },

    _init4: function(c, state) {
        this._init8(c, state, c.context, c.semanticContext);
    },

    _init5: function(c, state, semanticContext) {
        this._init8(c, state, c.context, semanticContext);
    },

    _init6: function(c, semanticContext) {
        this._init8(c, c.state, c.context, semanticContext);
    },

    _init7: function(c, state, context) {
        this._init8(c, state, context, c.semanticContext);
    },

    _init8: function(c, state, context, semanticContext) {
        this.state = state;
        this.alt = c.alt;
        this.context = context;
        this.semanticContext = semanticContext;
        this.reachesIntoOuterContext = c.reachesIntoOuterContext;
    },

    toString: function(){
        return this._key;
    }
};

_DECISION_STATE = {
    basicBlockStart: true, plusBlockStart:true, starBlockStart:true,
    plusLoopback:true, starLoopEntry:true, tokensStart:true
};

function isDecisionState(state){
    return _.has(_DECISION_STATE, state.type);
}

/**
 *
 * @param obj an object contains properties, check out prototype.initWithConfig()
 * @constructor
 */
function LexerATNConfig(obj){
    var init;
    if(arguments[0] instanceof LexerATNConfig){
        if(arguments.length === 2)
            init = this._init34;
        else if(arguments.length === 3){
            if(arguments[2] instanceof PredictionContext)
                init = this._init5;
            else
                init = this._init34;
        }
    }else{
        init = this._init12;
    }
    init.apply(this, arguments);
    this._key = JSON.stringify({
        s:this.state.stateNumber,
        a:this.alt,
        c:this.context == null? null: this.context.toString(),
        m:this.semanticContext.toString(),
        p:this.passedThroughNonGreedyDecision ? 1 : 0,
        l:this.lexerActionExecutor? this.lexerActionExecutor.toString() : null
    });
}

var DECISION_STATES = {startLoop: true, blockStart: true, TokenStart: true, plusLoopBack: true,
    starBlockStart:true, plusBlockStart:true, basicBlockStart:true};

LexerATNConfig.prototype = _.create(ATNConfig.prototype, {
    /**
     *
     * @param config
     */
    initWithConfig: function(config){
        this.alt = config.alt;
        this.semanticContext = config.semanticContext;
        this.reachesIntoOuterContext = config.reachesIntoOuterContext;
        this.lexerActionExecutor = config.lexerActionExecutor;
        this.passedThroughNonGreedyDecision = config.passedThroughNonGreedyDecision;


    },

    _init12: function(state, alt, context, lexerActionExecutor){
        ATNConfig.call(this, state, alt, context, SemanticContext.NONE);
        if(lexerActionExecutor !== undefined)
            this.lexerActionExecutor = lexerActionExecutor;
        this.passedThroughNonGreedyDecision = false;
    },

    _init34: function(c, state, lexerActionExecutor){
        ATNConfig.call(this, c, state, c.context, c.semanticContext);
        this.lexerActionExecutor = c.lexerActionExecutor;
        this.passedThroughNonGreedyDecision = this.checkNonGreedyDecision(c, state);
    },

    _init5: function(c, state, context){
        ATNConfig.call(this, c, state, context, c.semanticContext);
        this.lexerActionExecutor = c.lexerActionExecutor;
        this.passedThroughNonGreedyDecision = this.checkNonGreedyDecision(c, state);
    },

    checkNonGreedyDecision:function(source, target){
        //return checkNonGreedyDecision || isDecisionState(target);
        return source.passedThroughNonGreedyDecision ||
            target.type in DECISION_STATES && target.nonGreedy;

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

function ConfigHashSet(hashStringFunc){
    this.hashStringFunc = hashStringFunc;
    this.set = {};
}

ConfigHashSet.prototype = {
    add:function(o){
        this.set[this.hashStringFunc(o)] = o;
    },

    getOrAdd:function(o){
        var key = this.hashStringFunc(o);
        if(this.set.hasOwnProperty(key)){
            this.set[key] = o;
            return this.set[key];
        }
        this.set[key] = o;
        return o;
    },

    exists:function(o){
        return this.set.hasOwnProperty(this.hashStringFunc(o));
    }
};


function


ATNConfigSet(){
    this.configs = [];
    this.hasSemanticContext = false;
    this.readonly = false;
    this.fullCtx = true;
    this.cachedHashCode = -1;
    this.configLookup = new ConfigHashSet(
        function(atnConfig){
            return 'ss:'+ atnConfig.state.stateNumber +
                ',a:'+ atnConfig.alt + ', s:'+ atnConfig.semanticContext;
        });
}

ATNConfigSet.prototype = {
    logger: Log4js.getLogger('ATNConfigSet'),

    add:function(config, /* can be null */mergeCache){
        this.logger.debug('add('+ config +')');
        if ( this.readonly ) throw new Error("This set is readonly");
        if ( config.semanticContext!=SemanticContext.NONE ) {
            this.hasSemanticContext = true;
        }
        if (config.reachesIntoOuterContext > 0) {
            this.dipsIntoOuterContext = true;
        }
        this.logger.debug(this.configLookup);
        var existing = this.configLookup.getOrAdd(config);
        if(existing == config){
            this.cachedHashCode = -1;
            this.configs.push(config);  // track order here
            return true;
        }
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
    this.configLookup = new ConfigHashSet(function(o) {
        return o.hashCode? o.hashCode() : o.toString();
    });
}
OrderedATNConfigSet.prototype = _.create(ATNConfigSet.prototype);

function ATNSimulator(atn, sharedContextCache){
    this.atn = atn;
    this.sharedContextCache = sharedContextCache;
}

ATNSimulator.ERROR = new DFAState(new ATNConfigSet());
ATNSimulator.ERROR.stateNumber = 0xffffffff;

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



module.exports = {
    ATNConfig: ATNConfig,
    PredictionContext: PredictionContext,
    SingletonPredictionContext: SingletonPredictionContext,
    EmptyPredictionContext: EmptyPredictionContext,
    generateLexer:generateLexer,
    DFA: DFA,
    Transition: Transition
};
