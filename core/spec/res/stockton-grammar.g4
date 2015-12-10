

L: '\n' | '\r';

WS: ' '| '\t';

Number: ('0'..'9')+;

Id: Chr ( Chr | '0'..'9' )*;

fragment Chr: 'a'..'z'|'A'..'Z'|'_';

Comment
options {
    paraphrase="a single line comment";
}
    :   "//" (
            ~('\n'|'\r'|'\uffff')
        )*
    ;

Null: 'null' { System.out.println("this is null rule") }?;

Anychar: .;
