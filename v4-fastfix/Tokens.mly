// TODO: filter this to only what I need
%token
/* punctuation */ ARROW ASTERISK AT BACKSLASH BANG BAR DASH DBLARROW
DOT EQEQ GE GT LE LT PERCENT PLUS SEMI SLASH UNDER
EQ "="
COMMA ","
COLON ":"
LPAREN "(" RPAREN ")"
LBRACK "[" RBRACK "]"
LBRACE "{" RBRACE "}"
/* keywords */ TYPE DEF LET IN END EMPTY OR FOR CASE IF THEN WHEN
ELSE SHADOW FIX IS PI1 PI2
/* end of file */ EOF

%token <string> STRING
%token <bool> BOOL
%token <int> INTEGER
%token <string> ID CAPID        /* lower/uppercase identifiers */

%%
