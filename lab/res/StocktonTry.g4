grammar StocktonTry;
@header { package stocktonTry; }
L: '\n' | '\r';

WS: ' '| '\t';

Number: ('0'..'9')+;

Id: Chr ( Chr | '0'..'9' )*;

fragment Chr: 'a'..'z'|'A'..'Z'|'_';

Comment
    :   '//' (
            ~('\n'|'\r'|'\uffff')
        )*
    ;

Null: 'null' { true }?;

Anychar: .;

root: .+?;