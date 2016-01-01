var fs = require('fs');
var path = require('path');
var _ = require('lodash');

var fname = 'ATNGraph.html';
var row = 0;
var drawedStates = {};
var decisionStateSet = {};
var notDrawedStates = {}; 

function debugATN(atn, file){
	if(file)
		fname = file;
	_.each(atn.decisionToState, function(s){
		decisionStateSet[s.stateNumber] = true;
	});
	
	writeHTMLStart();
	fs.appendFileSync(fname, '<svg version="1.1" '+
     'baseProfile="full"' +
     //' width="3000" height="3000"'+
     ' xmlns="http://www.w3.org/2000/svg">\n'+
     '<defs></defs>\n'+
     '<g transform="translate(10, 30)">\n'
     );
	var lexStart = atn.states[0];
	_.each(atn.states, function(s){
			notDrawedStates[s.stateNumber] = s;
	});
	
	drawState(lexStart, 0);
	//draw fragment rules
	console.log('fragment rules %j', _.keys(notDrawedStates));
	while(true){
		var notDrawedSArr= _.sortBy(_.values(notDrawedStates), 'stateNumber');
		row++;
		if(notDrawedSArr.length === 0)
			break;
		drawState(notDrawedSArr[0], 0);
	}
	
	fs.appendFileSync(fname, '</g>\n</svg>\n</body></html>');
}



function drawState(state, col){
	var r = 30, x = col * 80 + r, y = row * 80 + r;
	var cCol = col, cRow = row;

	var circleClass = (_.has(decisionStateSet, state.stateNumber))? 'decision-state': '';
	fs.appendFileSync(fname, '<circle id="'+ col + ':' + row +'" class="'+ circleClass +'" cx="'+ x  +'" cy="'+ y +'" r="'+ (r - 1) +'" stroke="black" stroke-width="1"/>\n' + 
		'<text x="'+ x+'" y="'+ y +'">S: '+ state.stateNumber + '</text>\n'+ 
		'<text class="type" x="'+ x+'" y="'+ (y + 13) +'">'+ state.type + '</text>\n');
	if(state.type === 'ruleStop')
		fs.appendFileSync(fname, '<circle id="'+ col + ':' + row +'" class="'+ circleClass +'" cx="'+ x  +'" cy="'+ y +'" r="'+ (r - 4) +'" stroke="black" stroke-width="1"/>\n');
	if((state.type === 'ruleStart' || state.type === 'ruleStop' ) && state.ruleName)
		fs.appendFileSync(fname, '<text class="name" x="'+ x+'" y="'+ (y - 13) +'">'+ state.ruleName + '</text>\n');
	
	//console.log('state %s: transition num: %d', state.stateNumber, state.transitions.length);
	drawedStates[state.stateNumber] = [col, row];
	delete notDrawedStates[state.stateNumber];
	
	if(state.transitions && state.transitions.length > 0){
		_.each(state.transitions, function(tran, index){
				if(index > 0)
					row ++;
				var drawed = drawedStates[tran.target.stateNumber];
				if(tran.type === 'rule'){
					x = (cCol +1) * 80 + r;
					y = cRow * 80 + r;
					fs.appendFileSync(fname, '<circle class="drawed" cx="'+ x  +'" cy="'+ y +'" r="'+ (r - 1) +'" stroke="black" stroke-width="1"/>\n' + 
						'<text x="'+ x+'" y="'+ y +'">S: '+ tran.target.stateNumber + '</text>\n' +
						'<text class="type" x="'+ x+'" y="'+ (y + 13) +'">'+ tran.target.type + '</text>\n');
					line(cCol, cRow, col + 1, row, tran);
					drawState(tran.followState, col + 2);
					line(col + 1, cRow, col + 2, cRow);
					return;
				}
				if(!drawed){
					line(cCol, cRow, col + 1, row, tran);
					drawState(tran.target, col + 1);
				}else{
					line(cCol, cRow, drawed[0], drawed[1], tran);
				}
				
		});
	}
	return true;
}

function line(col0, row0, col1, row1, transition){
	var r = 30, x0 = col0 * 80 + r, y0 = row0 * 80 + r,
		x1 = col1 * 80 + r, y1 = row1 * 80 + r;
		
	var cx0, cx1, s;

	var text;
	if(row0 == row1){
		if(col0 +1 === col1){
			//short staight line
			s = 'M ' + (x0 + r) + ' '+ y0 +' H '+ (x1 - r);
			//var s = 'M ' + (x0 + r) + ' '+ y0 +' Q'+ ((x0 + x1)>>1)+' '+ (y1 - 10) +','+ (x1 - r) +' '+ y1;
			if(transition)
				drawTransition((x0 + x1)>>1, y0 - 10, transition);
				//text = '<text class="tran" x="'+ ((x0 + x1)>>1) +'"  y="'+ (y0 - 10) +'">' + textTransition(transition) +'</text>';
		}else{
		//we need a beautiful curve here
			if(x0 > x1){
				cx0 = x0 -r;
				cx1 = x1 +r;
			}else{
				cx0 = x0 +r;
				cx1 = x1 -r;
			}
			s = 'M ' + x0 + ' '+ (y0 + r) + ' C '+ cx0  +' '+ (y0 + 60) + ','+ cx1 +' '+ (y1 + 60) + ', ' + x1 +' '+ (y1 + r);
			//var s = 'M ' + x0 + ' '+ (y0 + r) +' Q' + ((x0 + x1) >>1)+' '+ (y1+ 60) + ','+  x1 +' '+ (y1 + r);
			if(transition)
				drawTransition((x0 + x1)>>1, y0 + r + 20, transition);
				//text = '<text class="tran" x="'+ ((x0 + x1)>>1) +'"  y="'+ (y0 + r + 20) +'">' + textTransition(transition) +'</text>';
		}
	}else{ // 2 straight lines will do just fine
		if(row1 > row0){
			if(col1 > col0){
				//var s = 'M ' + x0 + ' '+ (y0+r) + ' V '+ y1+ ' H '+ (x1 -r) ;
				s = 'M ' + x0 + ' '+ (y0+r) + ' C '+ x0 + ' '+ (y1+5)+ ', '+ (x0-5) +' '+ y1+ ', '+ (x1 -r) +' '+ y1;
				if(transition)
					drawTransition( (x0 + x1)>>1, y1-5, transition);
					//text = '<text class="tran" x="'+ ((x0 + x1)>>1) +'"  y="'+ (y1 - 5) +'">' + textTransition(transition) +'</text>';
			}
		}else{
			if(col0 > col1){
				s = 'M ' + x0 + ' '+ (y0 - r) + ' L '+ x1 + ' '+ (y1 + r);
				if(transition)
					drawTransition( (x0 + x1)>>1, (y0 + y1)>>1, transition);
					//text = '<text class="tran" x="'+ ((x0 + x1)>>1) +'"  y="'+ ((y0 + y1)>>1) +'">' + textTransition(transition) +'</text>';
			}else{
				s = 'M ' + (x0 + r) + ' '+ y0 +' C '+ (x1 +5)+' '+ y0 +','+ x1 +' '+(y0 +5)+ ','+ x1 +' '+ (y1 + r);
				if(transition)
					drawTransition( (x0 + x1)>>1, y0 - 5, transition);
					//text = '<text class="tran" x="'+ ((x0 + x1)>>1) +'"  y="'+ (y0 - 5) +'">' + textTransition(transition) +'</text>';
			}
		}
	}
	fs.appendFileSync(fname, '<path d="'+ s +'" class="transition" />');
	if(text)
		fs.appendFileSync(fname, text);
}

function drawTransition(x, y, tran){
	var type = tran.type === 'epsilon'? 'e': tran.type;
	var label = null;
	switch(tran.type){
	case 'atom':
		label = '"'+ tran.label + '"'; break;
	case 'range':
		label = '"'+ tran.from + '"-"'+ tran.to+ '"'; break;
	case 'set':
		label = tran.label; break;
	}
	fs.appendFileSync(fname, '<text class="tran" x="'+ x + '" y="'+ y+ '">'+
		type + '</text>');
	if(label)
		fs.appendFileSync(fname, '<text class="tran" x="'+ x + '" y="'+ (y - 15) + '">'+
			label + '</text>');
}

function writeHTMLStart(){
	var styles = fs.readFileSync(path.join(__dirname, 'ATNGraph.css'), 'utf-8');
	var s = '<!doctype html>\n';
	s += '<html>\n';
	s += '<head>\n';
	s += '<title>XTech SVG Demo</title>\n';
	s += '<style>\n';
	s += styles;
	s += '</style>\n';
	s += '<body>\n';
	fs.writeFileSync(fname, s);
}

exports.debugATN = debugATN;
