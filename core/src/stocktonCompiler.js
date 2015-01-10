var grmParser = require('./stockton-grammar-parser.js'),
	_ = require("lodash"),
	stUtil = require('./stockton-util.js'),
	RangeUtil = stUtil.RangeUtil,
	IntervalSet = require('./misc.js').IntervalSet,
	Interval = require('./misc.js').Interval,
	srt = require('./stocktonRuntime.js'),
	PredictionContext = srt.PredictionContext,
	SingletonPredictionContext = srt.SingletonPredictionContext,
	EmptyPredictionContext = srt.EmptyPredictionContext,
	ATNConfig = srt.ATNConfig,
	cycle = require('cycle');
	
/** @class AST */
AST = {
	getFirstChildWithType:function(ast, type){
		return _.find(ast.child, function(c){
				return c.type === type;
		});
	},
	getStartNode:function(ast){
		var child = ast.child;
		if(child && child.length > 0){
			return AST.getStart(child[0]);
		}else
			return ast;
	}
};

function Compiler(targetFileName){
	this.targetName = targetFileName;
	this.lexRuleASTMap = {};
	this.lexRuleASTs = [];
	//this.lexStartState = buildState();
	//this.lexRuleStates = [];
	//this.lexState = this.lexStartState;
	this.currentRuleName = null;
	this.preventEpsilonOptionalBlocks = [];
	this.preventEpsilonClosureBlocks = [];
	//LexerATNFactory.atn
	this.atn = {
		startState: null,
		states: [],
		ruleToStartState: null,
		ruleToStopState: null,
		decisionToState:[],
		defineDecisionState:function(s){
			this.decisionToState.push(s);
			return this.decisionToState.length -1;
		},
		addState:function(state){
			if (state != null) {
				state.atn = this;
				state.stateNumber = this.states.length;
			}
			this.states.push(state);
		},
		removeState:function(state){
			this.states[state.stateNumber] = null;
		}
	};
}

var EPSILON_TYPES = {
	epsilon: true, range: false, rule: true, predicate: true, action: true, 
	precedence: true, wildcard:false, notSet: false, set: false, atom: false
};
	
function isEpsilon(transition){
		if(!_.has(EPSILON_TYPES, transition.type)){
			throw new Error('undefined transition type: '+ transition.type);
		}
		return EPSILON_TYPES[transition.type];
}

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
	}
};

Compiler.prototype = {
	debugATN:function(){
		this.atn.states.forEach(function(state, index){
				var s = _.clone(state);
				delete s.transitions;
				console.log('state[%d]= %s', index, s.type);
				var str = '';
				_.each(s, function(v, f){
						str += f + ':'+ (typeof(v) == 'function'? '<f>' : v );
						str += ', ';
				});
				console.log('\t%s', str);
		});
		
		this.atn.decisionToState.forEach(function(ds, index){
				console.log('decisionToState[%d] = %s', index, ds);
		}, this);
	},
	
	compile:function(text){
		var parser = grmParser.create(text);
		this.grammar = parser;
		var ast = parser.parse().result;
		var tokenNum = 0;
		// fetch out all lexer rules: this.lexRuleASTs
		ast.forEach(function(ruleAst){
			if(ruleAst.type == 'lexRule'){
				this.lexRuleASTMap[ruleAst.name] = ruleAst;
				this.lexRuleASTs.push(ruleAst);
				if(!ruleAst.fragment){
					tokenNum++;
					console.log('find lex rule: %s', ruleAst.name);
				}
			}else if(ruleAst.type == 'tokens'){
				tokenNum += ruleAst.child.length;
			}
		}, this);
		this.atn.maxTokenType = tokenNum;
		console.log('tokenNum: %d', tokenNum);
		// CREATE ATN FOR EACH RULE
		this.createATN();
		
		// PERFORM GRAMMAR ANALYSIS ON ATN: BUILD DECISION DFAs
		this.analysisPipeline();
		return cycle.decycle(this.atn);
	},
	
	createATN:function(){
		// BUILD ALL START STATES (ONE PER MODE)
		// since I don't want to support MODE at this moment, there is only 1 start state needed
		this.atn.startState = this.newState('tokensStart');
		// INIT ACTION, RULE->TOKEN_TYPE MAP
		this.atn.ruleToTokenType = this.grammar.lexer.types;
		
		// CREATE ATN FOR EACH RULE
		this._createATN(this.lexRuleASTs);
		// atn.lexerActions = new LexerAction[indexToActionMap.size()];
		// for (Map.Entry<Integer, LexerAction> entry : indexToActionMap.entrySet()) {
		// 	atn.lexerActions[entry.getKey()] = entry.getValue();
		// }
		// LINK MODE START STATE TO EACH TOKEN RULE
		this.lexRuleASTs.forEach(function(ruleAST){ 
				if(!ruleAST.fragment){
					var s = this.atn.ruleToStartState[ruleAST.name];
					this._epsilon(this.atn.startState, s);
				}
		}, this);
		optimizeATN(this.atn);
		return this.atn;
	},
	
	_createATN:function(rules){
		this.createRuleStartAndStopATNStates();
		rules.forEach(function(ruleAST){
				this.currentRuleName = ruleAST.name;
				var block = AST.getFirstChildWithType(ruleAST, 'alts');
				var h = this.buildLexerATN(block);
				var start = this.atn.ruleToStartState[ruleAST.name];
				this._epsilon(start, h.left);
				var stop = this.atn.ruleToStopState[ruleAST.name];
				this._epsilon(h.right, stop);
				
		}, this);
	},
	
	_epsilon:function(a, b, prepend){
		if( a!=null ) {
			if(prepend)
				a.addTransition(0, {type:'epsilon', target: b});
			else
				a.addTransition({type:'epsilon', target: b});
		}
	},
	
	createRuleStartAndStopATNStates:function(){
		this.atn.ruleToStartState = {};
		this.atn.ruleToStopState = {};
		this.lexRuleASTs.forEach(function(ruleAST){
				var start = this.newState('ruleStart', ruleAST);
				var stop = this.newState('ruleStop', ruleAST);
				start.stopState = stop;
				//start.isPrecedenceRule = r instanceof LeftRecursiveRule;
				start.ruleName = ruleAST.name;
				stop.ruleName = ruleAST.name;
				this.atn.ruleToStartState[ruleAST.name] = start;
				this.atn.ruleToStopState[ruleAST.name] = stop;
		}, this);
	},
	/**
	@param type: basic, ruleStart, basicBlockStart, blockEnd, starLoopback. plusLoopback, tokensStart
	*/
	newState:function(type){
		var n = new ATNState(type);
		n.ruleName = this.currentRuleName;
		this.atn.addState(n);
		return n;
	},
	/* newTransition:funciton(type, targetState){
		return { type: type, target: targetState };
	} */
	
	/**
	transition's properties:
	{
		type - 'la'/'rule', 
		v - the char
		state - the next state
	}
	*/
	buildLexerATN:function(ast, /** useless */state){
		if(typeof(ast) === 'string'){//stringlit
			ast = getStringFromGrammarStringLiteral(ast);
			var left = this.newState('basic');
			var prev = left;
			var right;
			for (var i=0,l=ast.length; i<l; i++) {
				right = this.newState('basic');
				prev.addTransition({type: 'atom', target:right, label: ast.charAt(i)});
				prev = right;
			}
			return {left: left, right: right};
		}
		switch(ast.type){
			case 'range':
				//LexerATNFactory::range()
				var from = getStringFromGrammarStringLiteral(ast.from),
					to = getStringFromGrammarStringLiteral(ast.to);
				
				var left = this.newState('basic', from);
				var right = this.newState('basic', to);
				left.addTransition({type:'range', target: right, from: from, to: to});
				return {left:left, right:right};
			case 'not':
				var setAST = ast.child[0];
				var alts = [];
				setAST.child.forEach(function(setElementAST){
						//alts.add($setElement.start);
						alts.push(AST.getStartNode(setElementAST));
				}, this);
				//for lexer only, parser is different
				//Java: factory.set($start, alts, $invert);
				return this._lexerSet(setAST, alts, true);
			case 'wildcard':
				var left = this.newState('basic', ast);
				var right = this.newState('basic', ast);
				left.addTransition({type:'wildcard', target:right});
				return {left:left, right:right};
			case 'alt':
				if(ast.child.length == 0){
					//epsilon
					var left = this.newState('basic', ast);
					var right = this.newState('basic', ast);
					left.addTransition({type:'epsilon', target: right});
					return {left:left, right:right};
				}else{
					var els = this.buildLexerATN_child(ast);
					return this._elemList(els);
				}
			case 'alts':
				var alts = this.buildLexerATN_child(ast, state);
				if ( alts.length == 1 ) {
					return alts[0];
				}
				var start = this.newState('basicBlockStart', ast);
				if(alts.length > 1)
					this.atn.defineDecisionState(start);
				return this._makeBlock(start, ast, alts);
				
			case '*':
				var alts = this.buildLexerATN_child(ast.child[0], state);
				var star = this.newState('starBlockStart', ast);
				if ( alts.length >1 ) this.atn.defineDecisionState(star);
				var h = this._makeBlock(star, ast.child[0], alts);
				return this._star(ast, h);
				
			case '+':
				var alts = this.buildLexerATN_child(ast.child[0], state);
				var plus = this.newState('plusBlockStart', ast);
				if ( alts.length >1 ) this.atn.defineDecisionState(star);
				var h = this._makeBlock(plus, ast.child[0], alts);
				return this._plus(ast, h);
				
			case '?':
				var alts = this.buildLexerATN_child(ast.child[0], state);
				var start = this.newState('basicBlockStart', ast.child[0]);
				this.atn.defineDecisionState(start);
				var h = this._makeBlock(start, ast.child[0], alts);
				return this._optional(ast, h);
				
			case 'label':
			case 'tokenRef':
				if(ast.name == 'EOF'){
					var left = this.newState('basic', ast);
					var right = this.newState('basic', ast);
					left.addTransition({type: 'atom', target:right, label:'EOF'});
					return {left: left, right: right};
				}else{
					var ruleAST = this.lexRuleASTMap[ast.name];
					if(ruleAST == null){
						console.log("undefined rule: "+ ast.name);
						return null;
					}
					var start = this.atn.ruleToStartState[ast.name];
					var left = this.newState('basic');
					var right = this.newState('basic');
					var call = {type:'rule', ruleName:ast.name, target: start, followState: right};
					left.addTransition(call);
					return {left:left, right: right};
				}
			case 'sempred':
				return this._sempred(ast);
		}
	},
	buildLexerATN_child:function(ast, state){
		var ch = ast.child;
		var list = new Array(ch.length);
		for(var i=0,l=ch.length; i<l; i++){
			list[i] = this.buildLexerATN(ch[i], state);
		}
		return list;
	},
	_makeBlock:function(start, altsAST, alts){
		var end = this.newState('blockEnd', altsAST);
		start.endState = end;
		alts.forEach(function(alt){
				start.addTransition({type:'epsilon', target: alt.left});
				alt.right.addTransition({type:'epsilon', target: end});
				var opt = new TailEpsilonRemover(this.atn);
				opt.visit(alt.left);
		}, this);
		
		return {left: start, right: end};
	},
	/**
	 * From {@code (A)?} build either:
	 *
	 * <pre>
	 *  o--A->o
	 *  |     ^
	 *  o---->|
	 * </pre>
	 *
	 * or, if {@code A} is a block, just add an empty alt to the end of the
	 * block
	 */
	_optional:function(optAST, blk){
		var blkStart = blk.left;
		var blkEnd = blk.right;
		this.preventEpsilonOptionalBlocks.push({a: this.currentRuleName, b: blkStart, c: blkEnd});
		var greedy = true;
		//var greedy = ((QuantifierAST)optAST).isGreedy();
		blkStart.nonGreedy = !greedy;
		if ( blkStart!=null ) {
			var eps = {type: 'epsilon', target: blk.right};
			if(!greedy)
				blkStart.addTransition(0, eps);
			else
				blkStart.addTransition(eps);
		}
		optAST.atnState = blk.left;
		return blk;
	},
	
	/**
	 * From {@code (blk)*} build {@code ( blk+ )?} with *two* decisions, one for
	 * entry and one for choosing alts of {@code blk}.
	 *
	 * <pre>
	 *   |------------------ |
	 *   v             		|
	 *   entry--[o-blk-o]->loop  end
	 *   |                		^
	 *   ------------------------|
	 * </pre>
	 *
	 * Note that the optional bypass must jump outside the loop as
	 * {@code (A|B)*} is not the same thing as {@code (A|B|)+}.
	 	entry-> block -> loop
	 */
	 _star:function(starAST, elem){
		var blkStart = elem.left,
			blkEnd = elem.right;
		this.preventEpsilonClosureBlocks.push({a: this.currentRuleName, b: blkStart, c: blkEnd});
		
		var entry = this.newState('starLoopEntry', starAST);
		//entry.nonGreedy = !((QuantifierAST)starAST).isGreedy();
		entry.nonGreedy = false;
		this.atn.defineDecisionState(entry);
		var end = this.newState('loopEnd', starAST);
		var loop = this.newState('starLoopback', starAST);
		entry.loopBackState = loop;
		end.loopBackState = loop;
		
		var blkAST = starAST.child[0];
		//if ( ((QuantifierAST)starAST).isGreedy() ) {
		if(true /* greedy */){
			if (this.expectNonGreedy(blkAST)) {
				console.error('EXPECTED_NON_GREEDY_WILDCARD_BLOCK: %s',starAST.pos);
			}
			entry.addTransition({type: 'epsilon', target: blkStart});
			entry.addTransition({type: 'epsilon', target: end});
		}else{
			// if not greedy, priority to exit branch; make it first
			entry.addTransition({type: 'epsilon', target: end});
			entry.addTransition({type: 'epsilon', target: blkStart});
		}
		blkEnd.addTransition({type: 'epsilon', target: loop});
		loop.addTransition({type: 'epsilon', target: entry});
		starAST.atnState = entry;	// decision is to enter/exit; blk is its own decision
		return {left: entry, right: end};
	 },
	 
	 /**
	 * From {@code (blk)+} build
	 *
	 * <pre>
	 *   |---------|
	 *   v         |
	 *  [o-blk-o]->o->o
	 * </pre>
	 *
	 * We add a decision for loop back node to the existing one at {@code blk}
	 * start.
	 */
	 _plus:function (plusAST, blk) {
		var blkStart = blk.left;
		var blkEnd = blk.right;
		this.preventEpsilonClosureBlocks.push({a:this.currentRuleName, b: blkStart, c: blkEnd});

		var loop = this.newState('plusLoopback', plusAST);
		//loop.nonGreedy = !((QuantifierAST)plusAST).isGreedy();
		loop.nonGreedy = false;
		this.atn.defineDecisionState(loop);
		var end = this.newState('loopEnd', plusAST);
		blkStart.loopBackState = loop;
		end.loopBackState = loop;

		plusAST.atnState = blkStart;
		blkEnd.addTransition({type: 'epsilon', target: loop});		// blk can see loop back

		var blkAST = plusAST.child[0];
		if ( true /* greedy */) {
			if (this.expectNonGreedy(blkAST)) {
				console.error('EXPECTED_NON_GREEDY_WILDCARD_BLOCK: %s', plusAST.pos);
			}
			loop.addTransition({type: 'epsilon', target: blkStart});
			loop.addTransition({type: 'epsilon', target: end});
		}
		else {
			loop.addTransition({type: 'epsilon', target: end});
			loop.addTransition({type: 'epsilon', target: blkStart});
		}

		return {left: blkStart, right: end};
	},
	 
	
	_lexerSet:function(associatedAST, alts, invert){
		var left = this.newState('basic', associatedAST);
		var right = this.newState('basic', associatedAST);
		var set = new IntervalSet();
		alts.forEach(function(t){
			if(t.type === 'range'){
				set.add(getStringFromGrammarStringLiteral(t.from), 
					getStringFromGrammarStringLiteral(t.to));
			}else if(t.type === 'lexer_char_set'){
				set.addAll(getSetFromCharSetLiteral(t));
			}else if(typeof(t) === 'string'){
				var esc = getStringFromGrammarStringLiteral(t);
				if(esc.length === 1)
					set.add(esc);
				else
					throw new Error("Lexer doesn't support string which contains more than 1 character in a \"(NOT) SET\" sub rule, "+
						' "'+ t +
						'" at rule: '+ this.currentRuleName);
			}else if(t.type === 'tokenRef'){
				throw new Error("Lexer doesn't support TOKEN REFERENCE in a \"(NOT) SET\" sub rule," +
					' at rule: '+ this.currentRuleName);
			}
		}, this);
		if(invert)
			left.addTransition({type:'notSet', target:right, set:set});
		else{
			//todo only for "set", current "not set" does not go through this logic
		}
		return {left: left, right: right};
	},
	
	_sempred:function(pred) {
		//System.out.println("sempred: "+ pred);
		var left = this.newState('basic', pred);
		var right = this.newState('basic', pred);

		var p;
		//if (pred.getOptionString(LeftRecursiveRuleTransformer.PRECEDENCE_OPTION_NAME) != null) {
		//	int precedence = Integer.parseInt(pred.getOptionString(LeftRecursiveRuleTransformer.PRECEDENCE_OPTION_NAME));
		//	p = new PrecedencePredicateTransition(right, precedence);
		//}
		//else {
		//	boolean isCtxDependent = UseDefAnalyzer.actionIsContextDependent(pred);
		//	p = new PredicateTransition(right, currentRule.index, g.sempreds.get(pred), isCtxDependent);
		//}
		//todo
		p = {type: 'predicate', target: right, ruleName: this.currentRuleName, predContent:pred.content, isCtxDependent:true};

		left.addTransition(p);
		pred.atnState = left;
		return {left:left, right:right};
	},
	
	analysisPipeline:function(ast){
		var lr = new LeftRecursionDetector(ast, this.atn, this);
		lr.check();
		if ( lr.listOfRecursiveCycles.length > 0 ) return;
		this.analysis_processLexer();
		//processParser(); todo
	},
	
	analysis_processLexer:function(){
		this.lexRuleASTs.forEach(function(ast){
				if(ast.fragment)
					return;
				var look = this.LL1Analyzer(this.atn.ruleToStartState[ast.name], null, null);
				console.log('analysis_processLexer() look = %s\n', look.intervals.join(' , '));
				if (look.contains(-2))
					throw new Error('EPSILON_TOKEN in rule: '+ ast.name);
		}, this);
	},
	
	_elemList:function(els){
		var n = els.length;
		for (var i = 0; i < n - 1; i++) {
			var el = els[i];
			var tr = null;
			if ( el.left.transitions.length ==1 ) tr = el.left.transitions[0];
			var isRuleTrans = tr.type == 'rule';
			if(el.left.type === 'basic' && el.right.type === 'basic' &&
				tr != null && (isRuleTrans && tr.followState === el.right || tr.target === el.right))
			{
				if ( isRuleTrans ) tr.followState = els[i+1].left;
				else tr.target = els[i+1].left;
				this.atn.removeState(el.right);
			}else{
				//epsilon(el.right, els.get(i+1).left);
				if(el.right != null)
					el.right.addTransition({type:'epsilon', target: els[i+1].left});
			}
		}
		var first = els[0];
		var last = els[n - 1];
		if ( first==null || last==null ) 
			throw new Error("element list has first|last == null");
		return {left:first.left, right: last.right};
	},
	
	expectNonGreedy:function(blkAST){
		if ( this.blockHasWildcardAlt(blkAST) ) {
			return true;
		}

		return false;
	},
	
	blockHasWildcardAlt:function(block){
		 var ret = block.child.some(function(alt){
		 		 if(alt.type != 'alt') return false;
		 		 if(alt.child.length == 1){
		 		 	 var e = alt.child[0];
		 		 	 if(e.type === 'wildcard')
		 		 	 	 return true;
		 		 }
		 		 return false;
		 });
		 return ret;
	},
	
	HIT_PRED:0,
	
	LL1Analyzer:function(s, stopState, ctx){
		var r = new IntervalSet();
		var seeThruPreds = true; // ignore preds; get all lookahead
		var lookContext = ctx != null ? PredictionContext.fromRuleContext(s.atn, ctx) : null;
		this.LL1Analyzer_look(s, stopState, lookContext, r, {}, {}, seeThruPreds, true);
		return r;
	},
	
	LL1Analyzer_look:function(s, stopState, ctx, look, lookBusy, calledRuleStack,
		seeThruPreds, addEOF)
	{
		console.log('LL1Analyzer_look state %d\nlookBusy=%s', s.stateNumber, _.keys(lookBusy).join());
		var c = new ATNConfig(s, 0, ctx);
		if(lookBusy.hasOwnProperty(c))
			return;
		console.log('LL1Analyzer_look state %d continue', s.stateNumber);
		lookBusy[c] = true;
		if (s == stopState) {
			if (ctx == null) {
				look.add(-2);
				return;
			} else if (ctx.isEmpty() && addEOF) {
				look.add(-1);
				return;
			}
		}
		if(s.type == 'ruleStop'){
			if ( ctx==null ) {
                look.add(-2);
                return;
            } else if (ctx.isEmpty() && addEOF) {
				look.add(-1);
				return;
			}
			
			if ( ctx != PredictionContext.EMPTY ) {
				// run thru all possible stack tops in ctx
				for (var i = 0; i < ctx.size(); i++) {
					var returnState = this.atn.states[ctx.getReturnState(i)];

					var removed = _.has(calledRuleStack, returnState.ruleName);
					try {
						delete calledRuleStack[returnState.ruleName];
						this.LL1Analyzer_look(returnState, stopState, ctx.getParent(i), look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
					}
					finally {
						if (removed) {
							calledRuleStack[returnState.ruleName] = true;
						}
					}
				}
				return;
			}
		}
		var n = s.transitions.length;
        for (var i=0; i<n; i++) {
        		var t = s.transitions[i];
        		if(t.type == 'rule'){
        			if(_.has(calledRuleStack, t.target.ruleName))
        				continue;
        			var newContext = SingletonPredictionContext.create(ctx, t.followState.stateNumber);
				try{
					calledRuleStack[t.target.ruleName] = true;
					this.LL1Analyzer_look(t.target, stopState, newContext, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
				}finally {
					delete calledRuleStack[t.target.ruleName];
				}
			}else if(t.type == 'predicate' || t.type == 'precedence'){
				if ( seeThruPreds )
					this.LL1Analyzer_look(t.target, stopState, ctx, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
				else
					look.add(this.HIT_PRED);
        		}else if ( isEpsilon(t) ) {
				this.LL1Analyzer_look(t.target, stopState, ctx, look, lookBusy, calledRuleStack, seeThruPreds, addEOF);
			}else if(t.type == 'wildcard'){
        			look.addAll( IntervalSet.of(1, this.atn.maxTokenType) );
        		}else{
        			var set = Transition.label(t);
				if (set != null) {
					if (t.type == 'notSet') {
						set = set.complement(IntervalSet.of(1, this.atn.maxTokenType));
					}
					look.addAll(set);
				}
        		}
        }
	}
}

function ATNState(type){
	this.type = type;
	this.transitions = [];
	this.epsilonOnlyTransitions = false;
	this.stateNumber = -1;
}
ATNState.prototype = {
	addTransition:function(index, t){
		if(t === undefined){
			t = index;
			index = null;
		}
		if(this.transitions.length == 0)
			this.epsilonOnlyTransitions = (t.type == 'epsilon');
		else if(this.epsilonOnlyTransitions != (t.type == 'epsilon')){
			this.epsilonOnlyTransitions = false;
			console.log('ATN state %s has both epsilon and non-epsilon transitions.', this.type);
		}
		if(index === null)
			this.transitions.push(t);
		else
			this.transitions.splice(index, 0, t);
	}
};

var ATNVisitor = {
	visit:function(s){
		this.visit_(s, {});
	},
	visit_:function(s, visited){
		if(visited.hasOwnProperty(s.stateNumber))
			return;
		visited[s.stateNumber] = true;
		this.visitState(s);
		s.transitions.forEach(function(t){
				this.visit_(t.target, visited);
		}, this);
	}
};

function TailEpsilonRemover(atn){
	this._atn = atn;
}
_.extend(TailEpsilonRemover.prototype, ATNVisitor, {
	visitState:function(p){
		if(p.type == 'basic' && p.transitions.length === 1){
			var 	q = p.transitions[0].target;
			if(p.transitions[0].type === 'rule'){
				q = p.transitions[0].followState;
			}
			if(q.type === 'basic'){
				// we have p-x->q for x in {rule, action, pred, token, ...}
				// if edge out of q is single epsilon to block end
				// we can strip epsilon p-x->q-eps->r
				var trans = q.transitions[0];
				if(q.transitions.length == 1 && isEpsilon(trans) && ! trans.type == 'action'){
					var r = trans.target;
					if (r.type == 'blockEnd' || r.type == 'plusLoopBack' ||
						r.type == "starLoopback")
					{
						if(p.transitions[0].type == 'rule')
							p.transitions[0].followState = r;
						else
							p.transitions[0].target = r;
						this._atn.removeState(q);
					}
				}
			}
		}
	}
});

function optimizeATN(atn){
	_optimizeSets(atn);
	_optimizeStates(atn);
}

var _optTrans = { atom: true, range: true, set:true};

function _optimizeSets(atn){
	var removedStates = 0;
	var decisions = atn.decisionToState;
	_.each(decisions, function(decision){
		if(decision.ruleName && decision.ruleName.charAt(0).match(/[a-z]/))
			return;
		var setTransitions = new IntervalSet();
		for (var i = 0, l = decision.transitions.length; i<l; i++) {
			var epsTransition = decision.transitions[i];
			if(epsTransition.type === 'epsilon' || epsTransition.target.transitions.length != 1)
				continue;
			var transition = epsTransition.target.transition[0];
			if (!(transition.target.type === 'blockEndState'))
				continue;
			if(transition.type === 'notSet')
				continue;
			if( _.has(_optTrans, transition.type))
				setTransitions.add(i);
		}
		
		for(var i = setTransitions.intervals.length -1; i >= 0; i--){
			var interval = setTransitions.intervals[i];
			if(interval.length <= 1)
				continue;
			var blockEndState = decision.transitions[interval.a].target.transitions[0].target;
			var matchSet = new IntervalSet();
			for (var j = interval.a; j <= interval.b; j++) {
				var matchTransition = decision.transitions[j].target.transitions[0];
				if (matchTransition.type === 'notSet') {
					throw new Error("Not yet implemented.");
				} else {
					matchSet.addAll(Transition.label(matchTransition));
				}
			}
			
			var newTransition;
			if (matchSet.intervals.length == 1) {
				if (matchSet.size() == 1) {
					newTransition = {type: 'atom', target: blockEndState, label: matchSet.getMinElement()};
				} else {
					var matchInterval = matchSet.intervals[0];
					newTransition = {type: 'range', target: blockEndState, from: matchInterval.a, to: matchInterval.b};
				}
			} else {
				newTransition = {type: 'set', target: blockEndState, set: matchSet};
			}
            
			decision.transitions[interval.a].target.transitions[0] = newTransition;
			for (var j = interval.a + 1; j <= interval.b; j++) {
				var removed = decision.splice(interval.a + 1, 1);
				atn.removeState(removed.target);
				removedStates++;
			}
		}
	});
}

function _optimizeStates(atn){
	var compressed = [];
	var i = 0; // new state number
	atn.states.forEach(function(s){
		if ( s!=null ) {
			compressed.push(s);
			s.stateNumber = i; // reset state number as we shift to new position
			i++;
		}
	});
	atn.states.splice(0, atn.states.length);
	atn.states.push.apply(atn.states, compressed);
}

function getStringFromGrammarStringLiteral(literal){
	var buf = '';
	var i = 1; // skip first quote
	var n = literal.length -1; //  skip last quote
	while ( i < n ) { // scan all but last quote
		var end = i+1;
		if ( literal.charAt(i) == '\\' ) {
			end = i+2;
			if ( (i+1)>=n ) break; // ignore spurious \ on end
			if ( literal.charAt(i+1) == 'u' ) end = i+6;
		}
		if ( end>n ) break;
		var esc = literal.substring(i, end);
		var c = getCharValueFromCharInGrammarLiteral(esc);
		if ( c == -1 ) { buf += esc; }
		else buf += c;
		i = end;
	}
	return buf;
}

var ANTLRLiteralEscapedCharValue = {
	'n': '\n',
	'r': '\r',
	't': '\t',
	'b': '\b',
	'f': '\f',
	'\\': '\\',
	'\'': '\'',
	'"': '"',
	'\n': "\\n" ,
	'\r': "\\r" ,
	'\t': "\\t" ,
	'\b': "\\b" ,
	'\f': "\\f" ,
	'\\': "\\\\",
	'\'': "\\'"
};

function getCharValueFromCharInGrammarLiteral(cstr){
	switch ( cstr.length ) {
		case 1 :
			// 'x'
			return cstr.charAt(0); // no escape char
		case 2 :
			if ( cstr.charAt(0)!='\\' ) return -1;
			// '\x'  (antlr lexer will catch invalid char)
			if ( cstr.charAt(1) >= '0' &&  cstr.charAt(1) <= '9' ) return -1;
			var escChar = cstr.charAt(1);
			var charVal = ANTLRLiteralEscapedCharValue[escChar];
			if ( charVal == null ) return -1;
			return charVal;
		case 6 :
			// '\u1234'
			if ( cstr.substring(0, 2) != "\\u" ) return -1;
			var unicodeChars = cstr.substring(2);
			return String.fromCharCode(parseInt(unicodeChars, 16));
		default :
			return -1;
	}
}
Compiler.getStringFromGrammarStringLiteral = getStringFromGrammarStringLiteral;

function LeftRecursionDetector(ast, atn, compiler){
	this.g = ast;
	this.atn = atn;
	this.compiler = compiler;
	this.listOfRecursiveCycles = [];
	this.rulesVisitedPerRuleCheck = {};
}

LeftRecursionDetector.prototype = {
	check:function(){
		if(arguments.length > 0)
			return this._check.apply(this, arguments);
		_.each(this.atn.ruleToStartState, function(start, ruleName){
			//System.out.print("check "+start.rule.name);
			this.rulesVisitedPerRuleCheck = {};
			this.rulesVisitedPerRuleCheck[start.stateNumber] = true;
			//FASerializer ser = new FASerializer(atn.g, start);
			//System.out.print(":\n"+ser+"\n");

			this._check(ruleName, start, {});
		}, this);
		//System.out.println("cycles="+listOfRecursiveCycles);
		if ( ! _.isEmpty(this.listOfRecursiveCycles) ) {
			throw new Error('Left recursive cycles are encounted: ' + listOfRecursiveCycles);
		}
	},
	
	_check:function(enclosingRuleName, s, visitedStates){
		if(s.type === 'ruleStop') return true;
		if(visitedStates[s.stateNumber])
			return false;
		visitedStates[s.stateNumber] = true;
		var n = s.transitions.length;
		var stateReachesStopState = false;
		for (var i=0; i<n; i++) {
			var t = s.transitions[i];
			if ( t.type === 'rule' ) {
				var rt = t;
				var r = rt.ruleName;
				if ( this.rulesVisitedPerRuleCheck[t.target.stateNumber] ) {
					this.addRulesToCycle(enclosingRuleName, r);
				}
				else {
					// must visit if not already visited; mark target, pop when done
					this.rulesVisitedPerRuleCheck[t.target.stateNumber] = true;
					// send new visitedStates set per rule invocation
					var nullable = this._check(r, t.target, {});
					// we're back from visiting that rule
					delete this.rulesVisitedPerRuleCheck[t.target.stateNumber];
					if ( nullable ) {
						stateReachesStopState |= this._check(enclosingRuleName, rt.followState, visitedStates);
					}
				}
			}
			else if ( isEpsilon(t) ) {
				stateReachesStopState |= this._check(enclosingRuleName, t.target, visitedStates);
			}
			// else ignore non-epsilon transitions
		}
		return stateReachesStopState;
	},
	
	addRulesToCycle:function(enclosingRuleName, targetRuleName){
		console.log("left-recursion to "+targetRuleName+" from "+enclosingRuleName);
		var foundCycle = false;
		_.each(this.listOfRecursiveCycles, function(rulesInCycle){
			// ensure both rules are in same cycle
			if (_.has(rulesInCycle, targetRuleName)) {
				rulesInCycle[enclosingRuleName] = true;
				foundCycle = true;
			}
			if (_.has(rulesInCycle, enclosingRuleName)) {
				rulesInCycle[targetRuleName] = true;
				foundCycle = true;
			}
		}, this);
		if ( !foundCycle ) {
			var cycle = {};
			cycle[targetRuleName] = true;
			cycle[enclosingRuleName] = true;
			this.listOfRecursiveCycles.push(cycle);
		}
	}
};





module.exports = {
	Compiler: Compiler
};
