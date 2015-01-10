var LL = require('./baseLLParser.js'),
	//_ = require("./underscore-min.js");
	_ = require('lodash');

var keywordMap = {
	'options': 0,
	'protected': 1,
	'returns': 2,
	'fragment': 1,
	'tokens': 3
}
function scanToken(lex){
    var other = false;
    var c = lex.la();
    switch(c){
    case ' ':
    case '\t':
    case '\r':
    case '\f':
    case '\n':
        lex.advance();
            lex.bnfLoop(0, function(){
                    var c = lex.la();
                    return c == ' ' || c == '\t' || c == '\r' || c === '\f' || c === '\n';
            });
        lex.emitToken('WS', 1);
        break;
    case '/':
        if(this.la(2) == '*')
            comment(lex);
        else if(this.la(2) == '/')
            lineComment(lex);
        else{
            lex.advance();
            lex.emitToken(c);
        }
        break;
    case '"':
    case "'":
        stringLit(lex);
        break;
    case '[':
    case ']':
    case '{':
    case '}':
    case '(': case ',':
    case ')': case ':': case ';': case '!': case '?': case '+': case '*': case '~': case '@' :
    case '|':
        lex.advance();
        lex.emitToken(c);
        break;
    case '-':
    		if(lex.la(2) === '>'){
    			this.advance(2);
    			this.emitToken('->');
    			break;
    		}
    case '.':
    		if(lex.la(2) == '.'){
    			lex.advance(2);
    			lex.emitToken('..');
    			return;
    		}else{
    			var c2 = lex.la(2);
    			if(c2 >= '0' && c2 <= '9' )
    				number(lex);
    			else{
    				lex.advance();
    				lex.emitToken(c);
    			}
        	}
        return;
    default:
        if(c >= '0' && c<= '9'){
			number(lex);
		}else if(c >= 'a' && c<= 'z' || c >= 'A' && c <= 'Z' || c === '_' || c === '$'){
			id(lex);
		}
    }
    
}
function stringLit(lex){
    var start = lex.la();
    lex.advance();
    if(lex.predChar(start, start)){
        tripleQuote(lex);
        return;
    }
    lex.bnfLoop(0, function(){
            return lex.la() != start;
    }, function(){
        var c = this.la();
        if(c == '\\')
            this.advance();
        else if(c === '\n')
            this.unexpect('"\n" in string literal');
        this.advance();
    });
    lex.advance();
    lex.emitToken('stringLit');
}

function tripleQuote(lex){
    var startChar = lex.advance(2);
    lex.bnfLoop(0, function(){
            return !lex.predChar(startChar, startChar, startChar);
    }, function(){
        var c = this.la();
        if(c == '\\')
            this.advance();
        this.advance();
    });
    lex.advance(3);
    lex.emitToken('stringLit');
}

function comment(lex){
    var channel = 1;
    lex.advance(2);
    var content = '', type = 'comment';
    if(lex.la() == '*' && lex.la(2) != '/'){
        type = 'doc';
        channel = 2;
        lex.advance();
    }
    
    lex.bnfLoop(0, function(){
            return !this.predChar('*', '/');
    }, function(){
        content += lex.advance();
    });
    lex.advance(2);
    var t = lex.emitToken(type, channel);
    t.text(content);
}

function lineComment(lex){
    lex.advance(2);
    var content = '';
    lex.bnfLoop(0, function(){
            return this.la() != '\n';
    }, function(){
        content += lex.advance();
    });
    lex.advance();
    var t = lex.emitToken('comment', 1);
    t.text(content);
}

function isReguarExpress(lex){
    switch(lex.lastToken.type){
    case 'id':
    case 'null':
    case 'bool':
    case 'this':
    case 'number':
    case 'stringLit':
    case ']':
    case ')':
        return false;
    default:
        return true;
    }
}

function regex(lex){
    lex.advance();
    lex.bnfLoop(1, function(){
            return this.la() != '/';
    }, function(){
        if(this.la() == '\\')
            this.advance();
        this.advance();
    });
    lex.match('/');
    lex.emitToken('regex');
}

function id(lex){
    var text = lex.advance();
    lex.bnfLoop(0, function(){
    			
            var c = this.la();
            return c >= 'a' && c<= 'z' || c >= 'A' && c <= 'Z' || c === '_' || 
                c === '$' || c >= '0' && c <= '9';
    }, function(){
        text += this.advance();
    });
    if(keywordMap.hasOwnProperty(text))
    		lex.emitToken(text);
    	else
    		lex.emitToken('id');
}

var numberSuffix = {'f':true, 'F':true, 'd':true, 'D':true};

var HEX_CHAR = {'a':true, A:true, B:true, 'b':true, C:true, c:true, 'd':true, 'D':true, e:true, E:true, f:true, F:true};

var NOT_CHILD_TYPES = {tokenRef:true, range:true, stringLit:true};

function number(lex){
    var d = lex.advance();
    if(d === '0' && lex.la() === 'x'){
        hex(lex);
        return;
    }else if(d >= '0' && d <= '9'){
        lex.bnfLoop(0, function(){
                var c = this.la();
                return c >= '0' && c<= '9';
        });
    }else if(d === '-'){
    		lex.advance();
    }
    if(d == '.')
		lex.bnfLoop(0, function(){
				var c = this.la();
				return c >= '0' && c<= '9';
		});
    var c = lex.la();
    if(c in numberSuffix)
        lex.advance();
    lex.emitToken('number');
}

function hex(lex){
    lex.advance();
    lex.bnfLoop(2, function(){
            var c = this.la();
            return c >= '0' && c <= '9' || c in HEX_CHAR;
    });
    lex.emitToken('number');
}

var grammar = {
	AST:[],
	
    root: function(){
    		if(this.predToken('tokens'))
    			this.rule('tokenDef');
        this.rule('blockContent', true);
        this.match('EOF');
    },
    
    tokenDef:function(){
    		this.match('tokens');
    		this.match('{');
    		var tokens = [];
    		this.bnfLoop(0, function(){return this.inTokens('id', ',')},
    			function(){
    				if(this.predToken('id'))
    					tokens.push(this.advance().text());
    				else
    					this.advance();
    			});
    		this.match('}');
    		return {type:'tokens', child: tokens};
    },
    
    blockContent: function(hasRule){
    		var s = [];
        this.bnfLoop(0, function(){ return !this.predToken('}')},
        function(){
            if(this.predToken('{')){
                this.rule('block');
            }else if(hasRule && this.predRule('isRule')){
                s.push(this.rule('rule').result);
            }else{
                this.rule('other');
            }
        });
        return s;
    },
    block: function(){
        this.advance();
        this.rule('blockContent', false);
        var content = this.ruleText().substring(1);
        this.match('}');
        if(this.predToken('?')){
        		this.advance();
        		return { type:'sempred', content:content};
        }
        return null;
    },
    
    rule:function(){
    		if(this.inTokens('protected', 'fragment')){
    			var fragment = true;
    			this.advance();
    		}
        var name = this.match('id').text();
        if(this.inTokens('!'))
        		this.advance();
        this.bnfLoop(0, function(){
				return this.inTokens("[", "returns");
		}, function(){
				if(this.inTokens('returns'))
					this.advance();
				this.match('[');
				this.bnfLoop(0, function(){ return !this.predToken(']'); });
				this.match(']');
			});
        if(this.predToken('{')){
        		this.rule('block');
        }
        this.bnfLoop(0, function(){
				return this.inTokens('@');
		}, function(){
			this.rule('action');
		});
        if(this.predToken('options'))
        		this.rule('options');
        	else
        		this.match(':');
        var choice = this.rule('alts').result;
        this.match(';');
        var chr0 = name.charAt(0);
        return { type: ((chr0 >= 'A' && chr0 <= 'Z')? 'lexRule':'parserRule'),fragment: fragment, name: name, child: [choice]};
    },
    
    alts:function(){
    		var child = [];
    		child.push({type:'alt', child:this.rule('alt').result});
    		this.bnfLoop(0, function(){ return this.predToken("|"); },
    			function(){
    				this.advance();
    				child.push({type:'alt', child:this.rule('alt').result});
    			});
    		return {
    			type:'alts',
    			child: child
    		};
    },
    
    alt:function(){
    		this.bnfLoop(0, function(){ return !this.inTokens("|", ";", ")"); },
    			function(){
    				this.rule('element').result;
    			});
    },
    /**
    tokenRef, regex, range, stringLit, not, alts, wildcard, bnf, label, set
    */
    element:function(){
    		var ret = null;
    		if(this.predToken('id', ':')){
    			var label = this.advance();
    			this.advance();
    		}
    		if(this.predToken('id')){
    			ret = this.rule('tokenRef').result;
    		}else if(this.predToken('[')){
    			//todo
    			this.unexpect(this.la());
    			this.rule('regex');
    		}else if(this.predToken('stringLit')){
    			if(this.predToken('stringLit', '..'))
    				ret = this.rule('range').result;
    			else	{
    				var s = this.advance();
    				ret = s.text();
    			}
    		}else if(this.predToken('~')){
    			ret = this.rule('not').result;
    		}else if(this.predToken('(')){
    			this.advance();
    			ret = this.rule('alts').result;
    			this.match(')');
    		}else if(this.predToken('.')){
    			this.advance();
    			ret = {
    				type: 'wildcard'
    			};
    		}else if(this.predToken('{')){
        		ret = this.rule('block').result;
    		}else if(this.predToken('options')){
    			this.rule('options');
    			ret = null;
    		}else{
    			this.unexpect(this.la());
    		}
    		if(this.inTokens('?','+','*')){
    			ret = this.rule('bnfSuffix', ret).result;
    		}
    		//if(ret){
    		if(label && ret)
    			return {type:'label', child:[ret]};
    		else{
    			return ret;
    		}
    		//}
    },
    
    tokenRef:function(){
    		var id = this.advance();
    		var ast = {
				type:'tokenRef',
				name: id.text()
			};
    		return ast;
	},
	
	bnfSuffix:function(content){
		var bnf = this.advance();
    		return {
			type:bnf.text(),
			pos: bnf.position2str(),
			child: [content.type ==='alts'? content : {type:'alts', child:[ content ]}]
		};
	},
    /**
    todo
    */
    regex:function(){
    		this.match('[');
    		if(this.inTokens('^')){
    			this.advance();
    			var choice = this.rule('charChoice');
    			return {
    				type: 'not',
    				child: choice
    			};
    		}else{
    			this.rule('charChoice');
    		}
    },
    
    charChoice:function(){
    		
    },
    
    options:function(){
    		this.advance();
    		this.rule('block');
    		
    		this.match(':');
    		return null;
    },
    
    not:function(){
    		this.match('~');
    		if(this.inTokens('(')){
    			this.advance();
    			var ret = [ this.rule('element').result ];
    			this.bnfLoop(0, function(){ return this.predToken("|"); },
    			function(){
    				this.advance();
    				ret.push( this.rule('element').result );
    			});
    			this.match(')');
    		}else{
    			var ret = [ this.rule('element').result ];
    		}
    		//var ret = this.rule('element').result;
    		//if(! NOT_CHILD_TYPES.hasOwnProperty(ret.type))
    		//	throw new Error('"~" does not support expression other than: '+ _.keys(NOT_CHILD_TYPES));
    		return {
    			type:'not',
    			child:[{
    				type:'set',
    				child: ret
    			}]
    		};
    },
    
    range:function(){
    		var f = this.advance();
    		this.match('..');
    		var t = this.advance();
    		return { type:'range', from:f.text(), to:t.text()};
    },

    isRule:function(){
		if(this.inTokens('protected', 'fragment')){
			return true;
		}
		var name = this.match('id');
		if(this.inTokens('!'))
        		this.advance();
		this.bnfLoop(0, function(){
				return this.inTokens("[", "returns");
		}, function(){
				if(this.inTokens('returns'))
					this.advance();
				this.match('[');
				this.bnfLoop(0, function(){ return !this.predToken(']'); });
				this.match(']');
			});
		if(this.predToken('{')){
				this.rule('block');
		}
		this.bnfLoop(0, function(){
				return this.inTokens('@');
		}, function(){
			this.rule('action');
		});
		if(this.predToken('options'))
			this.rule('options');
		else
			this.match(':');
    },
    action:function(){
        this.match('@');
        this.match('id');
        this.rule('block');
        return null;
    },
    other:function(){
    		this.advance();
    		return null;
    }
};
exports.create = function(text){
    var parser = new LL.Parser(text, scanToken, grammar);
    
    parser.parse = function(){
    		return parser.rule("root");
    }
    
    /* parser.onAST = function(stack, ast){
        if(!Array.isArray(ast)){
            ast.start = stack.startToken.pos[0];
            ast.stop = stack.stopToken.pos[1];
            ast.line = stack.startToken.pos[2];
        }
        
        return ast;
    } */
    return parser;
};
