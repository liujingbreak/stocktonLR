//'use strict';

var _ = require("lodash");
var util = require('util');
var LL = require('./baseLLParser');
var 	Log4js = require('log4js');
var sutil = require('./stockton-util');
var IntervalSet = require('./misc.js').IntervalSet;

var logger = Log4js.getLogger('stocktonRuntime');

var debug = true;
var EOF = LL.Lexer.prototype.EOF;
/*
var Transition = {
	label:function(tran){
		switch(tran.type){
			case 'atom':
				return IntervalSet.of(tran.label);
			case 'range':
				return IntervalSet.of(tran.from, tran.to);
			case 'set':
				return tran.set;
			default:
				return null;
		}
	},

	matches:function(tran, symbol, minVocabSymbol, maxVocabSymbol) {
		switch(tran.type){
			case 'atom':
				return tran.label == symbol;
			case 'set':
				return tran.set.contains(symbol);
			case 'notSet':
				return symbol >= minVocabSymbol
					&& symbol <= maxVocabSymbol
					&& !tran.set.contains(symbol);
			case 'wildcard':
				return symbol >= minVocabSymbol && symbol <= maxVocabSymbol;
			case 'range':
				return symbol >= tran.from && symbol <= tran.to;
			case 'predicate':
			case 'precedence':
			case 'epsilon':
			case 'rule':
			case 'action':
				return false;
		}
	}
};
*/

var RETURN_FALSE = function(){
	return false;
};

var TransitionMatches = {
	precedence: RETURN_FALSE,
	predicate: RETURN_FALSE,
	epsilon: RETURN_FALSE,
	action: RETURN_FALSE,
	atom:function(tran, symbol){
		return tran.label === symbol;
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
	label:function(tran){
		switch(tran.type){
			case 'atom':
				return IntervalSet.of(tran.label);
			case 'range':
				return IntervalSet.of(tran.from, tran.to);
			case 'set':
				return tran.set;
			default:
				return null;
		}
	},

	matches:function(tran, moreArgs){
		return TransitionMatches[tran.type].apply(this, arguments);
	}
};

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

PredictionContext.merge = function(/*PredictionContext*/ a, /*PredictionContext*/ b,
		 rootIsWildcard, mergeCache)
{
	if(!( a!=null && b!=null))
		throw new Error('assertion failure in PredictionContext.merge()'); // must be empty context, never null

	// share same graph if both same
	if ( a==b || a.equals(b) ) return a;
    
	if ( a instanceof SingletonPredictionContext && b instanceof SingletonPredictionContext) {
		return PredictionContext.mergeSingletons(a,b, rootIsWildcard, mergeCache);
	}
    
	// At least one of a or b is array
	// If one is $ and rootIsWildcard, return $ as * wildcard
	if ( rootIsWildcard ) {
		if ( a instanceof EmptyPredictionContext ) return a;
		if ( b instanceof EmptyPredictionContext ) return b;
	}
    
	// convert singleton so both are arrays to normalize
	if ( a instanceof SingletonPredictionContext ) {
		a = new ArrayPredictionContext(a);
	}
	if ( b instanceof SingletonPredictionContext) {
		b = new ArrayPredictionContext(b);
	}
	return mergeArrays(a, b, rootIsWildcard, mergeCache);
};

_.extend(PredictionContext, {
	mergeSingletons: function(a,b,rootIsWildcard, mergeCache){
		if ( mergeCache!=null ) {
			var previous = mergeCache.get(a,b);
			if ( previous!=null ) return previous;
			previous = mergeCache.get(b,a);
			if ( previous!=null ) return previous;
		}

		var rootMerge = PredictionContext.mergeRoot(a, b, rootIsWildcard);
		if ( rootMerge!=null ) {
			if ( mergeCache!=null ) mergeCache.put(a, b, rootMerge);
			return rootMerge;
		}

		if ( a.returnState==b.returnState ) { // a == b
			var parent = PredictionContext.merge(a.parent, b.parent, rootIsWildcard, mergeCache);
			// if parent is same as existing a or b parent or reduced to a parent, return it
			if ( parent == a.parent ) return a; // ax + bx = ax, if a=b
			if ( parent == b.parent ) return b; // ax + bx = bx, if a=b
			// else: ax + ay = a'[x,y]
			// merge parents x and y, giving array node with x,y then remainders
			// of those graphs.  dup a, a' points at merged array
			// new joined parent so create new singleton pointing to it, a'
			var a_ = SingletonPredictionContext.create(parent, a.returnState);
			if ( mergeCache!=null ) mergeCache.put(a, b, a_);
			return a_;
		}
		else { // a != b payloads differ
			// see if we can collapse parents due to $+x parents if local ctx
			var singleParent = null;
			if ( a==b || (a.parent!=null && a.parent.equals(b.parent)) ) { // ax + bx = [a,b]x
				singleParent = a.parent;
			}
			if ( singleParent!=null ) {	// parents are same
				// sort payloads and use same parent
				var payloads = [a.returnState, b.returnState];
				if ( a.returnState > b.returnState ) {
					payloads[0] = b.returnState;
					payloads[1] = a.returnState;
				}
				var parents = [singleParent, singleParent];
				var a_ = new ArrayPredictionContext(parents, payloads);
				if ( mergeCache!=null ) mergeCache.put(a, b, a_);
				return a_;
			}
			// parents differ and can't merge them. Just pack together
			// into array; can't merge.
			// ax + by = [ax,by]
			var payloads = [a.returnState, b.returnState];
			var parents = [a.parent, b.parent];
			if ( a.returnState > b.returnState ) { // sort by payload
				payloads[0] = b.returnState;
				payloads[1] = a.returnState;
				parents = [b.parent, a.parent];
			}
			var a_ = new ArrayPredictionContext(parents, payloads);
			if ( mergeCache!=null ) mergeCache.put(a, b, a_);
			return a_;
		}
	},
	
	mergeRoot:function( a, b, rootIsWildcard)
	{
		if ( rootIsWildcard ) {
			if ( a == PredictionContext.EMPTY ) return PredictionContext.EMPTY;  // * + b = *
			if ( b == PredictionContext.EMPTY ) return PredictionContext.EMPTY;  // a + * = *
		}
		else {
			if ( a == PredictionContext.EMPTY && b == PredictionContext.EMPTY ) return PredictionContext.EMPTY; // $ + $ = $
			if ( a == PredictionContext.EMPTY ) { // $ + x = [$,x]
				var payloads = [b.returnState, PredictionContext.EMPTY_RETURN_STATE];
				var parents = [b.parent, null];
				var joined =
					new ArrayPredictionContext(parents, payloads);
				return joined;
			}
			if ( b == PredictionContext.EMPTY ) { // x + $ = [$,x] ($ is always first if present)
				var payloads = [a.returnState, EMPTY_RETURN_STATE];
				var parents = [a.parent, null];
				var joined =
					new ArrayPredictionContext(parents, payloads);
				return joined;
			}
		}
		return null;
	},
	calculateHashCode:function(parent, returnState){
		if(Array.isArray(parent)){
			return PredictionContext._calculateHashCode(parent, returnState);
		}
		return JSON.stringify({
			p:parent.toString(),
			r:returnState
		});
	},
	
	_calculateHashCode:function( parents, returnStates) {
		var ps = [];
		parents.forEach(function(pa){
			ps.push(pa.hashCode());
		});
		
		return JSON.stringify({
			ps:ps,
			rs:returnStates
		});
	},
	calculateEmptyHashCode:function(){
		return '';
	}
});


PredictionContext.EMPTY_RETURN_STATE = 0xffffffff;
PredictionContext.prototype = {
	EMPTY_RETURN_STATE: PredictionContext.EMPTY_RETURN_STATE,

	isEmpty:function(){
		return this == PredictionContext.EMPTY;
	},
	toString:function(){
		return this.hashCode();
	},
	hasEmptyPath:function(){
		return this.getReturnState(this.size() - 1) == this.EMPTY_RETURN_STATE;
	},
	
	equals:function(o){
		return this === o;
	},
	
	hashCode: function() {
		return this.cachedHashCode;
	}
};

function SingletonPredictionContext(parent, returnState){
	PredictionContext.call(this, 
		parent != null? PredictionContext.calculateHashCode(parent, returnState) : PredictionContext.calculateEmptyHashCode());
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
	},
	
	equals:function(o) {
		if (this == o) {
			return true;
		}
		else if ( !(o instanceof SingletonPredictionContext) ) {
			return false;
		}

		if ( this.hashCode() !== o.hashCode() ) {
			return false; // can't be same if hash is different
		}

		var s = o
		return returnState === s.returnState &&
			(parent!=null && parent.equals(s.parent));
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
			return this.returnState;
		}
});
PredictionContext.EMPTY = new EmptyPredictionContext();

/*
@param a SingletonPredictionContext
*/
function ArrayPredictionContext(parents, returnStates){
	if(arguments.length === 1){
		var a = arguments[0];
		return ArrayPredictionContext([a.parent], [a.returnState]);
	}
	PredictionContext.call(this, PredictionContext.calculateHashCode(parents, returnStates));
	if(parents!=null && parents.length>0)
		throw new Error();
	
	if(returnStates!=null && returnStates.length>0)
		throw new Error();
//	System.err.println("CREATE ARRAY: "+Arrays.toString(parents)+", "+Arrays.toString(returnStates));
	this.parents = parents;
	this.returnStates = returnStates;
}

ArrayPredictionContext.prototype = _.create(PredictionContext.prototype, {
	isEmpty:function(){
		return this.returnStates[0]=== PredictionContext.EMPTY_RETURN_STATE;
	},
	size:function() {
		return this.returnStates.length;
	},
	getParent:function(index){
		return this.parents[index];
	},
	getReturnState:function(index){
		return this.returnStates[index];
	},
	
	equals:function(o){
		if (this == o) {
			return true;
		}
		else if ( !(o instanceof ArrayPredictionContext) ) {
			return false;
		}

		if ( this.hashCode() != o.hashCode() ) {
			return false; // can't be same if hash is different
		}

		var a = o;
		return sutil.Arrays_equals(returnStates, a.returnStates) &&
		       sutil.Arrays_equals(parents, a.parents);
	}
});
			


	
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

/**
 *
 * @param obj an object contains properties, check out prototype.initWithConfig()
 * @constructor
 */
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
			this.logger.debug('1. target='+ target);
			if (target == null) {
				target = this.computeTargetState(input, s, t);
			}
			this.logger.debug('2. target='+ util.inspect(target));
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
			/* todo */this.accept(input, lexerActionExecutor, this.startIndex,
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
			var to = this._addDFAState(q);
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
	
	_addDFAState:function(configs){
		if(configs.hasSemanticContext)
			throw new Error('failed to assert !configs.hasSemanticContext');
		var proposed = new DFAState(configs);
		var firstConfigWithRuleStopState = null;

		configs.configs.some(function(c){
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
							new LexerATNConfig({state: target,
									alt: c.alt,
									context: c.context,
									semanticContext: c.semanticContext,
									reachesIntoOuterContext: c.reachesIntoOuterContext,
									lexerActionExecutor: lexerActionExecutor}),
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
		_.some(configs.configs, function(c){
				if(c.state.type === 'ruleStop'){
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
	LexerATNSimulator: LexerATNSimulator,
	Transition: Transition
};
