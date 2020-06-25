{
    open PolyParse        (* The type token is defined in parser.mli *)
    exception Eof
}
rule token = parse
    [' ' '\t']     { token lexbuf }     (* skip blanks *)
    | ['\n' ]        { EOL }
    | ['0'-'9']+ as lxm { INT(int_of_string lxm) }
    | ['a'-'z']  as lxm { VAR(lxm) }
    | '+'            { PLUS }
    | '-'            { MINUS }
    | '*'            { TIMES }
    | '^'            { POWER }
    | eof            { EOL }