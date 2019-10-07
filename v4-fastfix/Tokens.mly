// TODO: filter this to only what I need
%token
/* punctuation */ AT DOT COMMA UNDER SEMI COLON BANG PLUS DASH ASTERISK SLASH
PERCENT ARROW DBLARROW BAR LE LT GE GT EQ EQEQ RPAREN LPAREN
RBRACE LBRACE RBRACK LBRACK BACKSLASH
/* keywords */ TYPE DEF LET IN END EMPTY OR FOR DO CASE IF THEN WHEN
ELSE SHADOW AS
/* end of file */ EOF

%token <string> STRING
%token <bool> BOOL
%token <int> INTEGER
%token <string> ID CAPID        /* lower/uppercase identifiers */

%%
