var stGrammarParser = require('../src/stockton-grammar-parser.js'),
	LL = require('../src/baseLLParser.js'),
	sc = require('../src/stocktonCompiler'),
	debugATN = require('../src/debugATN.js'),
	Compiler = sc.Compiler,
	stRuntime = require('../src/stocktonRuntime.js'),
	cycle = require('cycle'),
	util = require('util'),
	fs = require('fs'),
	path = require('path'),
	PredictionContext  = stRuntime.PredictionContext,
	logger = require('log4js');
	
var log = logger.getLogger('testSpec');
//log.setLevel('INFO');
logger.getLogger('ATNConfigSet').setLevel('INFO');
logger.getLogger('LexerATNSimulator').setLevel('INFO');

describe('Compiler', function(){
	xit('getStringFromGrammarStringLiteral() should work', function(){
		var escaped = Compiler.getStringFromGrammarStringLiteral(
			'\'this is new line:\\n, this is tab: \\t, this is "\\\\u0061": \\u0061\'');
		console.log(escaped);
		expect(escaped).toEqual('this is new line:\n, this is tab: \t, this is "\\\\u0061": a');
	});
});

describe('stockton grammar parser', function(){
		
	beforeEach(function(){
			this.str = fs.readFileSync(path.join( __dirname, 'res/stockton-grammar.g'), {encoding: 'utf-8'});
	});
	
	xit('can generate AST', function(){
		var parser = stGrammarParser.create(this.str);
		parser.verbose();
		var ast = parser.parse();
		console.log('-------------- log ------------');
		console.log(ast);
		expect(ast).toBeDefined();
		console.log('-------------- AST result ------------');
		console.log(JSON.stringify(ast.result, null, '  '));
	});
		
	xit('compiler process AST -> ATN', function(){
		var compiler = new Compiler();
		var atn0 = compiler.compile(this.str);
		//compiler.debugATN();
		expect(atn0).toBeDefined();
		console.log('-------------- ATN ------------');
		console.log('atn: %j', atn0);
		
		var atn = cycle.retrocycle(atn0);
		var graphPath = path.join(__dirname, '../build/ATNGraph.html');
		debugATN.debugATN(atn, graphPath);
	});
	
	it('LexerATNSimulator.match can work', function(){
		var compiler = new Compiler();
		var atn = cycle.retrocycle(compiler.compile(this.str));
		
		var _decisionToDFA = [], i = 0;
		atn.decisionToState.forEach(function(s){
			_decisionToDFA.push(new stRuntime.DFA({atnStartState: s, decision: i}));
		});
		var _interp = new stRuntime.LexerATNSimulator(atn, _decisionToDFA, null);
		
		var result = [];
		var input = new LL.Lexer('987 null');
		var type = _interp.match(input, 0);
		result.push(type);
		
		while(type !== -1){
			log.info('input offset '+ input.offset + ' type '+ type);
			type = _interp.match(input, 0);
			result.push(type);
		}

		expect(result).toEqual([
			2, 1, 5, -1
		]);
	});
	
	xit('compiler can generate Lexer parser based on ATN', function(){
		var compiler = new Compiler();
		var atn = cycle.retrocycle(compiler.compile(this.str));
		//var scanToken = stRuntime.generateLexer(atn);
	})
});


