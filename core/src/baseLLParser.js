
var assert = require('assert');
var EOF = -1;

function mixin(target, obj){
	for(f in obj){
		target[f] = obj[f];
	}
}
if (typeof Object.create != 'function') {
    (function () {
        var F = function () {};
        Object.create = function (o) {
            if (arguments.length > 1) { throw Error('Second argument not supported');}
            if (o === null) { throw Error('Cannot set a null [[Prototype]]');}
            if (typeof o != 'object') { throw TypeError('Argument must be an object');}
            F.prototype = o;
            return new F;
        };
    })();
}
function extend(subclass, superclass, override){
	subclass.prototype = Object.create(superclass.prototype);
	subclass._super = superclass.prototype;
	subclass.superclass = superclass;
	mixin(subclass.prototype, override);
}
function UnexpectLex(msg){
    var err = new Error(msg);
    err.name = 'UnexpectLex';
    return err;
}
//extend(UnexpectLex, Error);

function UnexpectToken(msg){
    var err = Error(msg);
    //err.message = msg;
    err.name = 'UnexpectToken';
    return err;
}
//extend(UnexpectToken, Error);

//assert(new UnexpectToken('').constructor === UnexpectToken);

function Lexer(str, callback){
    this.offset = 0;
    this.lineno = 1;
    this.col = 1;
    
    this.startOff = this.offset;
    this.startLine = this.lineno;
    this.startCol = this.col;
    
    this.input = new Array(str.length);
    this.startToken = null;
    this.lastToken = null;
    this.tokenIndex = 0;
    this.callback = callback;
    this.types = {'EOF': EOF, 'SOF': -2};
    this.typeIdx = 0;
    this.typeNames = [];
    
    this.escapedCol = null;
    this.escapedOffset = null;
    this.escapedLine = null;
    
    //this.nextChar = null;
    for(var i = 0, l = str.length; i<l; i++){
        this.input[i] = str.charAt(i);
    }
}
exports.Lexer = Lexer;
Lexer.prototype = {
    classname:'Lexer',
    EOF: EOF,
    moreToken:function(){
        try{
            while(true){
                var oldTokenIdx = this.tokenIndex;
                var c = this.la();
                if(c == EOF){
                    this.emitToken('EOF');
                    return;
                }
                if(this.callback)
                    this.callback(this, this, c);
                else
                    throw new Error('not implemented');
                if(this.tokenIndex == oldTokenIdx){
                    
                    //no emitToken called, consider as escaped char
                    if(this.escapedOffset == null){
                        this.escapedOffset = this.startOff;
                        this.escapedLine = this.startLine;
                        this.escapedCol = this.startCol;
                        //console.log('here ='+ this.tokenIndex + ', offset='+ this.startOff);
                    }
                    //throw new Error('lexer must emit at least 1 token everytime');
                    this.advance();
                    this.startOff = this.offset;
                    this.startLine = this.lineno;
                    this.startCol = this.col;
                }else{
                    break;
                }
            }
        }catch(e){
            if(e.name == 'UnexpectLex'){
                console.log('Lexer fails due to above exception');
            }
            //todo handle expection
            throw e;
        }
    },
    
    range:function(chr, charFrom, charTo){
        return chr >= charFrom && chr <= charTo;
    },
    
    bnfLoop:function(leastTimes, predFunc, subRule){
        if(subRule === undefined)
            subRule = this.advance;
        while(this.la() != EOF){
            try{
                var pred = predFunc.call(this, this);
                if(pred === undefined){
                    throw new Error('predicate function must return boolean value');
                }
            }catch(e){
                if(e.name == UnexpectLex)
                    pred = false;
                else
                    throw e;
            }
            if(!pred)
                break;
            if(subRule)
                subRule.call(this);
            leastTimes--;
        }
        if(leastTimes > 0)
            this.unexpect(' end of BNF ( not reach leastTimes:'+ leastTimes +')');
    },
    next:function(){
        var c = this.la(1);
        this.advance();
        return c;
    },
    advance:function(num){
        if(num === undefined)
            num = 1;
        for(var i = num; i; i--){
            
            if( this.input[this.offset] == '\n'){
                this.lineno++;
                this.col = 1;
            }else if(this.input[this.offset] != '\r'){
                this.col++;
            }
            this.offset++;
            
        }
        return this.input[this.offset - 1];
        //console.log('advance offset=%d', this.offset);
    },
    match:function(chr){
        if(this.la() != chr)
            this.unexpect('');
        else
            this.advance();
    },
    unexpect:function(msg){
        chr = this.la();
        if(chr == EOF)
            chr = 'EOF';
        console.log('unexpect '+ (msg?msg:'') +' char at line '+ this.lineno + ', offset '+ this.offset + 
            ' "'+ chr + '"');
        throw new UnexpectLex(JSON.stringify({chr: chr, lineno: this.lineno, offset: this.offset}, null, '  '));
    },
    /** look ahead
    @param index starts from 1, default 1
    */
    la:function(index){
        if(index === undefined)
            index = 1;
        var pos = this.offset + index - 1;
        if( pos >= this.input.length)
            return EOF;
        //console.log('la() this=%s, offset=%d, pos=%d', this.classname,this.offset, pos);
        return this.input[pos];
    },
    
    /** look back */
    lb:function(index){
        if(index === undefined)
            index = 1;
        var pos = this.offset - index;
        return this.input[pos];
    },
    
    predChar:function(c, c2, c3){
        for(var i = 1, l = arguments.length; i<= l; i++){
            if(this.la(i) != arguments[i - 1 ])
                return false;
        }
        return true;
    },
    
    predString:function(str){
        for(var i = 1, l = str.length; i<= l; i++){
            if(this.la(i) != str.charAt(i - 1 ))
                return false;
        }
        return true;
    },
    
    unknown:function(c){
        if(this._unknown == null)
            this._unknown = c;
        else
            this._unknown += c;
    },
    
    /**
    @param stype token type name
    @param channel default channel is 0, if you want to indicate this token as skipped token like white space, put it as any number other than 0
    @return newly created token
    you can manupilate returned token like set text by calling .text(string) 
    */
    emitToken:function(stype, channel){
        if(this.escapedOffset != null){
            var tk = this._emitToken('<UNK>', 0, this.escapedOffset, this.escapedLine, this.escapedCol,
                this.startOff, this.startLine, this.startCol);
            this.escapedOffset = null;
            this.escapedLine = null;
            this.escapedCol = null;
            //console.log('UNK: '+ tk);
        }
        var token = this._emitToken.apply(this, arguments);
        //console.log('#'+ token.toString());
        //if(this._verbose)
        //		console.log(' emit token: '+ stype);
        return token;
    },
    
    _emitToken:function(stype, channel, startOff, startLine, startCol, endOff, endLine, endCol){
        if(startOff === undefined){
            startOff = this.startOff;
            startLine = this.startLine;
            startCol = this.startCol;
            endOff = this.offset;
            endLine = this.lineno;
            endCol = this.col;
        }
        
        if(channel === undefined)
            channel = 0;
        var token = new Token({
            type:this._tokenType(stype), 
            pos:[startOff, endOff, startLine, endLine, startCol, endCol],
            idx: this.tokenIndex++,
            channel: channel,
            prev: this.lastToken,
            next:null
        }, this);
        //console.log('# emit %s %j', stype, token.pos);
        if(this.lastToken)
            this.lastToken.next = token;
        this.lastToken = token;
        if(!this.startToken)
            this.startToken = token;
        this.startOff = endOff;
        this.startLine = endLine;
        this.startCol = endCol;
        return token;
    },
    
    /**
    @param token | startOffset, endOffset
    */
    text:function(token){
        if(arguments.length == 1 && token instanceof Token){
            var pos = token.pos;
            return this.input.slice(pos[0], pos[1]).join('');
        }else{
            return this.input.slice(arguments[0], arguments[1]).join('');
        }
    },
    /**
    create a new type number or return existing type number
    */
    _tokenType:function(stype){
        if(this.types.hasOwnProperty(stype))
            return this.types[stype];
        var n = this.types[stype] = this.typeIdx ++;
        this.typeNames[n] = stype;
        return n;
    }
};

function Token(json, lexer){
    mixin(this, json);
    this.lexer = lexer;
}
Token.prototype = {
    typeName:function(){
        if(this.type == EOF)
            return 'EOF';
        return this.lexer.typeNames[this.type];
    },
    text:function(text){
        if(text !== undefined)
            this._text = text;
        if(this._text)
            return this._text;
        else
            return this.rawText();
    },
    rawText:function(){
        return this.lexer.text(this);
    },
    toString:function(){
        return JSON.stringify({
                type: this.type,
                typeName: this.typeName(),
                channel: this.channel,
                idx: this.idx,
                pos: this.position2str(),
                text: this.text()
        }, null, '  ');
    },
    position2str:function(){
        return ' [offset '+ this.pos[0] +' - '+ this.pos[1] +
        '], [line '+ this.pos[2] +' - '+ this.pos[3] +
        '], [columen '+ this.pos[4] +' - '+ this.pos[5]+ ']';
    }
}

function Parser(str, lexerCallback, parserGrammar, channel){
    this.lexer = new Lexer(str, lexerCallback);
    this.currIdx = null;
    this.nestedPredCnt = 0;
    this.channel = channel === undefined? 0 : channel;
    this.ruleStackCurr = null;
    this.stackLevel = -1;
    this.grammar = parserGrammar;
    
    this.astNames = {};
    if(this.grammar.AST)
        for(var i=this.grammar.AST.length; i; i--)
            this.astNames[this.grammar.AST[i-1]] = true;
    
    this.lexer.moreToken();
    var next = this.lexer.startToken;
    while(next.type != EOF && next.channel !== this.channel){
        this.lexer.moreToken();
        next = next.next;
    }
    this._next = next;
    
    this.SOF = new Token({
            type:this.lexer._tokenType('SOF'), 
            pos:[0, 0, 0, 0, 0, 0],
            idx: -1,
            channel: 0,
            prev: this.lexer.lastToken,
            next:null
     }, this);
}
exports.Parser = Parser;
Parser.prototype = {
    classname:'Parser',
    typeName:function(nType){
        if(nType == EOF)
            return 'EOF';
        return this.lexer.typeNames[nType];
    },
    tokenType:function(sType){
        return this.lexer.types[sType];
    },
    /**
    call this after parsing process is finished, otherwise you won't get a correct result of a complete token list
    */
    getMaxTokenType:function(){
    		return this.lexer.typeNames.length;
    },
    //nextToken:function(){
    //    if(!this._next){
    //        this.lexer.moreToken();
    //        this._next = this.lexer.startToken;
    //    }else{
    //        if(!this._next.next)
    //            this.lexer.moreToken();
    //        this._next = this._next.next;
    //    }
    //    return this._next;
    //},
    la:function(index){
        if(index === undefined)
            index = 1;
        //console.log©250('this._next %s %j', this.typeName(this._next.type), this._next.pos); 
        var next = this._next;
        var i = index -1;
        if(next.channel !== this.channel)
            i++;
        for(; i; i--){
            if(next.type == EOF)
                return next;
            if(!next.next)
                this.lexer.moreToken();
            if(next.next == null){
                console.log('token does not have next '+ next);
                debugger;
                this.lexer.moreToken();
            }
            next = next.next;
            if(next.channel !== this.channel)
                i++;//more rounds
        }
        return next;
    },
    
    lb:function(index){
        if(index === undefined)
            index = 1;
        var prev = this._next;
        for(var i = index; i; i--){
            var prev = prev.prev;
            if(!prev)
                return this.SOF;
            if(prev.channel !== this.channel)
                i++;
        }
        return prev;
    },
    
    inTokens:function(typeName1){
        var ntype = this.la().type;
        for(var i=0,l=arguments.length; i<l; i++){
            if(ntype == this.tokenType(arguments[i]))
                return true;
        }
        return false;
    },
    
    predToken:function(typeName1, typeName2, typeName3){
        var types = arguments;
        return this._isTypes.call(this, function(i){
                return this.tokenType(types[i]);
            }, arguments.length);
    },
    
    predRule:function(predFuncName, param){
        var arr = [];
        for(var i=1,l=arguments.length;i<l;i++)
            arr.push(arguments[i]);
        return this._predRule(predFuncName, arr);
    },
    
    _predRule:function(predFuncName, paramArray){
        return this._pred(this.grammar[predFuncName], paramArray);
    },
    
    pred:function(predFunc, param){
        var arr = [];
        for(var i=1,l=arguments.length;i<l;i++)
            arr.push(arguments[i]);
        return this._pred(predFunc, arr);
    },
    
    _pred:function(predFunc, paramArray, condition){
        this.nestedPredCnt++;
        
        var next = this._next;
        try{
            var ret = predFunc.apply(this, paramArray);
            return ret !== false;
        }catch(e){
            if(e.name == 'UnexpectToken'){
                return false;
            }else
                throw e;
        }finally{
            this._next = next;
            this.nestedPredCnt--;
        }
    },
    
    isPredicate:function(){
        return this.nestedPredCnt >0 ;
    },
    
    _isTypes:function(typesCallback, typesNum){
        var next = this._next;
        for(var i =0, l = typesNum; i<l; i++){
            var ntype = typesCallback.call(this, i);
            
            if(next.type != EOF && next.channel !== this.channel){
            		if(!next.next)
            			this.lexer.moreToken();
                next = next.next;
                //console.log(next.toString());
                i--;//more rounds
                continue;
            }
            if(next.type != ntype){
                //console.log('Not found: next.type=%s\n\texpect=%s', 
                //    next, this.typeName(ntype));
                return false;
            }
            if(next.type == EOF){
                debugger;
                return i == l-1;
            }
            if(!next.next)
                this.lexer.moreToken();
            next = next.next;
        }
        return true;
    },
    
    /**
    @param predFunc must explicitly return a true or /false
    @param subRuleFunc (optional) once predFunc returns true, this function will be execute, 
    the returned value will be regarded as loop's returned value, can be null
    */
    bnfLoop:function(leastTimes, predFunc, subRuleFunc){
        //var elements = [];
        if(typeof(leastTimes) != 'number')
        		throw new Error('wrong arguments type to call bnfLoop()');
        if(subRuleFunc === undefined)
            subRuleFunc = this.advance;
        if(typeof subRuleFunc == 'string')
            var isRuleName = true;
        
        for(var i=0;this.la().type != EOF;i++){
            try{
                var next = this._next;
                var pred = this._pred(predFunc);
                this._next = next;
                //if(pred === undefined){
                //		this.log('predicate function must return boolean value');
                //    throw new Error('predicate function must return boolean value');
                //}
            }catch(e){
                if(e.name == 'UnexpectToken')
                    pred = false;
                else
                    throw e;
            }
            if(!pred)
                break;
            if(isRuleName)
                this.rule(subRuleFunc);
            else
                subRuleFunc.call(this);
            
            //elements.push(subRule.call(this));
            leastTimes--;
        }
        if(leastTimes > 0)
            throw new UnexpectToken('unexpect end of BNF '+ this.la());
        return i;
    },
    
    
    match:function(typeName1){
    		var r;
        for(var i=0,l=arguments.length; i<l; i++){
            var next = this._next;
            var tk = this.advance();
            r = tk;
            if(tk.type != this.tokenType(arguments[i])){
                this._next = next;
                throw new UnexpectToken('expect "'+ arguments[i] +'", unexpect token: '+ tk);
            }
        }
        return r;
    },
    
    unexpect:function(token){
        throw new UnexpectToken('unexpect Token '+ token);
    },
    
    advance:function(num){
        if(num === undefined)
            num = 1;
        var last = this._next;
        if(!this.isPredicate() && last.type !== EOF){
            this.ruleStackCurr.child.push(last.text());
        }
        this._next = this.la(num+1);
        return last;
    },
    
    text:function(startOffset, endOffset){
        return this.lexer.text(startOffset, endOffset);
    },
    /**
    if user defined rule function returns nothing (undefined),
    parse will still return an array (this.ruleStackCurr.child) contains all child AST nodes
    
        1) if this rule name is in grammar's "AST" list, parser will automatically
            build an AST tree for this rule, and will be added to parent tree
            e.g. 
            {   type: 'parentRuleName',
                child:[
                    { type: 'funcName', child: [...] }
                ]
            }
            
        2) if this rule name is not in grammar's AST list, parser will not build AST
            tree for this rule, but instead it will move all its child AST nodes to parent
            rule's AST tree'
            e.g.
            {   type: 'parentRuleName',
                child:[ parentChild1, parentChild2, thisRuleChild...]
            }
    @param funcName name of this rule
    */
    rule:function(funcName, arg0){
        this._inRule(funcName);
        var ret;
        try{
            var args = [];
            var parser = this;
            for(var i=1,l=arguments.length; i<l; i++){
                args.push(arguments[i]);
            }
            ret = this.grammar[funcName].apply(this, args);
            
            var result = this._wrapResult(ret);
            return result;
        }finally{
            this._outRule(funcName, ret);
        }
    },
    
    _inRule:function(name){
        this.stackLevel++;
        var stack = {
            startToken: this.la(),
            ruleName: name,
            parent: null,
            stopToken: null
            // child: array of child's ast
            // ast
        };
        if(this.ruleStackCurr)
            stack.parent = this.ruleStackCurr;
        this.ruleStackCurr = stack;
        if(!this.isPredicate()){
            stack.child = [];
            if(this._verbose){
                var debugMsg = '';
                for(var i=0,l=this.stackLevel; i<l; i++)
                    debugMsg += ' |';
                debugMsg += '-::'+ name +':: ';
                debugMsg += stack.startToken.typeName() + stack.startToken.position2str();
                console.log(debugMsg);
            }
            if(this.listener && this.listener.ruleIn)
                this.listener.ruleIn.call(this, name);
        }
    },
    
    _wrapResult:function(ret){
        var r = ret === undefined? this.ruleStackCurr.child : ret;
        var start = this.ruleStackCurr.startToken.pos,
            stop = this.lb().pos,
            parser = this;
        return this.onReturn({
            ruleName: this.ruleStackCurr.ruleName,
            result: r,
            start:start,
            stop:stop,
            //startToken: stack.startToken,
            //stopToken: stack.stopToken,
            text: function(){
                return parser.text(start[0], stop[1]);
            }
        });
    },

    _outRule:function(name, ret){
        this.ruleStackCurr.stopToken = this.lb();
        if(!this.isPredicate()){
            if(this.listener && this.listener.ruleOut)
                this.listener.ruleOut.call(this, name);
            var p = this.ruleStackCurr.parent;
            if(!p) return;
            
            var pc = p.child, tc = this.ruleStackCurr.child;
            if(ret != null){
                ret = this.onAST(this.ruleStackCurr, ret);
                if(Array.isArray(ret)){
                    for(var i=0,l=ret.length; i<l;i++)
                        pc.push(ret[i]);
                }else
                    pc.push(ret);
            }else if(ret === undefined){
                if (this.grammar.AST === undefined || this.astNames[name]){
                    var ast = {type:name, child: tc};
                    pc.push(this.onAST(this.ruleStackCurr, ast));
                }else{
                    for(var i=0,l=tc.length; i<l; i++)
                    pc.push(tc[i]);
                }
            }
        }
        this.ruleStackCurr = this.ruleStackCurr.parent;
        this.stackLevel--;
    },
     
    log:function(arg){
        //if(this.isPredicate())
        //    return;
        var debugMsg = '';
        for(var i= -1 ,l=this.stackLevel; i<l; i++)
            debugMsg += ' |';
        debugMsg += '- '+ arg;
        var args = [debugMsg];
        for(var i=1,l=arguments.length;i<l;i++)
            args.push(arguments[i]);
        console.log.apply(console, args);
        //console.log(debugMsg);
    },
       
    ruleText:function(){
        return this.text(this.ruleStackCurr.startToken.pos[0], this.lb().pos[1]);
    },
    verbose:function(){
        this._verbose = true;
        this.lexer._verbose = true;
        console.log('verbose');
    },
    /**
    override this method, if you want to implement AST build process globally
    @param stack an object contains current rule stack properties, which might be useful
        stack = {
            startToken:
            ruleName: ,
            parent: ,
            stopToken: 
        }
    @param astOrRet could either be the returned no-null value returned by user defined rule,
    or an automatically generated AST object whose normal structure is
    {
        type: <rule name>,
        child: [
            <subrule AST>
        ]
    }
    */
    onAST:function(stack, astOrRet){
        return astOrRet;
    },
    onReturn:function(ret){
        return ret;
    },
};

