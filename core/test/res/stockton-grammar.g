

L: '\n' | '\r';

WS: ' '| '\t';

Number: ('0'..'9')+;

fragment Chr: 'a'..'z'|'A'..'Z'|'_';

Id: Chr ( Chr | '0'..'9' )*;

Comment
options {
    paraphrase="a single line comment";
}
    :   "//" (
            ~('\n'|'\r'|'\uffff')
        )*
    ;

Null: 'null' { parseKeyword() }?;

Anychar: .;
