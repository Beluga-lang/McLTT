prog: RPAREN
##
## Ends in an error in state: 0.
##
## prog' -> . prog [ # ]
##
## The known suffix of the stack is as follows:
##
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: TYPE ZERO
##
## Ends in an error in state: 3.
##
## atomic_obj -> TYPE . AT INT [ ZERO VAR TYPE RPAREN RETURN NAT LPAREN INT IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## TYPE
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: TYPE AT ZERO
##
## Ends in an error in state: 4.
##
## atomic_obj -> TYPE AT . INT [ ZERO VAR TYPE RPAREN RETURN NAT LPAREN INT IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## TYPE AT
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: SUCC RPAREN
##
## Ends in an error in state: 6.
##
## obj -> SUCC . obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## SUCC
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC RPAREN
##
## Ends in an error in state: 7.
##
## obj -> REC . obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LPAREN RPAREN
##
## Ends in an error in state: 10.
##
## atomic_obj -> LPAREN . obj RPAREN [ ZERO VAR TYPE RPAREN RETURN NAT LPAREN INT IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LPAREN
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LET ZERO
##
## Ends in an error in state: 11.
##
## obj -> LET . param EQ obj IN obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LET
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN ZERO
##
## Ends in an error in state: 12.
##
## param -> LPAREN . VAR COLON obj RPAREN [ LPAREN EQ ARROW ]
##
## The known suffix of the stack is as follows:
## LPAREN
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN VAR ZERO
##
## Ends in an error in state: 13.
##
## param -> LPAREN VAR . COLON obj RPAREN [ LPAREN EQ ARROW ]
##
## The known suffix of the stack is as follows:
## LPAREN VAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN VAR COLON RPAREN
##
## Ends in an error in state: 14.
##
## param -> LPAREN VAR COLON . obj RPAREN [ LPAREN EQ ARROW ]
##
## The known suffix of the stack is as follows:
## LPAREN VAR COLON
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN VAR COLON INT SUCC
##
## Ends in an error in state: 17.
##
## param -> LPAREN VAR COLON obj . RPAREN [ LPAREN EQ ARROW ]
##
## The known suffix of the stack is as follows:
## LPAREN VAR COLON obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA ZERO
##
## Ends in an error in state: 19.
##
## obj -> fnbinder . params ARROW obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## fnbinder
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN VAR COLON INT RPAREN ZERO
##
## Ends in an error in state: 20.
##
## obj -> fnbinder params . ARROW obj [ RPAREN RETURN IN EOF END COLON BAR ]
## params -> params . param [ LPAREN ARROW ]
##
## The known suffix of the stack is as follows:
## fnbinder params
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LAMBDA LPAREN VAR COLON INT RPAREN ARROW RPAREN
##
## Ends in an error in state: 21.
##
## obj -> fnbinder params ARROW . obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## fnbinder params ARROW
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LET LPAREN VAR COLON INT RPAREN ZERO
##
## Ends in an error in state: 28.
##
## obj -> LET param . EQ obj IN obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LET param
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LET LPAREN VAR COLON INT RPAREN EQ RPAREN
##
## Ends in an error in state: 29.
##
## obj -> LET param EQ . obj IN obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LET param EQ
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LET LPAREN VAR COLON INT RPAREN EQ INT SUCC
##
## Ends in an error in state: 30.
##
## obj -> LET param EQ obj . IN obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LET param EQ obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LET LPAREN VAR COLON INT RPAREN EQ INT IN RPAREN
##
## Ends in an error in state: 31.
##
## obj -> LET param EQ obj IN . obj [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LET param EQ obj IN
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: LPAREN INT SUCC
##
## Ends in an error in state: 33.
##
## atomic_obj -> LPAREN obj . RPAREN [ ZERO VAR TYPE RPAREN RETURN NAT LPAREN INT IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## LPAREN obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT SUCC
##
## Ends in an error in state: 35.
##
## obj -> REC obj . RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN ZERO
##
## Ends in an error in state: 36.
##
## obj -> REC obj RETURN . VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR ZERO
##
## Ends in an error in state: 37.
##
## obj -> REC obj RETURN VAR . DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT RPAREN
##
## Ends in an error in state: 38.
##
## obj -> REC obj RETURN VAR DOT . obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT SUCC
##
## Ends in an error in state: 39.
##
## obj -> REC obj RETURN VAR DOT obj . BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR VAR
##
## Ends in an error in state: 40.
##
## obj -> REC obj RETURN VAR DOT obj BAR . ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO ZERO
##
## Ends in an error in state: 41.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO . DARROW obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW RPAREN
##
## Ends in an error in state: 42.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW . obj BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT SUCC
##
## Ends in an error in state: 43.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj . BAR SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR ZERO
##
## Ends in an error in state: 44.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR . SUCC VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC ZERO
##
## Ends in an error in state: 45.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC . VAR COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC VAR ZERO
##
## Ends in an error in state: 46.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR . COMMA VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC VAR COMMA ZERO
##
## Ends in an error in state: 47.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA . VAR DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC VAR COMMA VAR ZERO
##
## Ends in an error in state: 48.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR . DARROW obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC VAR COMMA VAR DARROW RPAREN
##
## Ends in an error in state: 49.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW . obj END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: REC INT RETURN VAR DOT INT BAR ZERO DARROW INT BAR SUCC VAR COMMA VAR DARROW INT SUCC
##
## Ends in an error in state: 50.
##
## obj -> REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj . END [ RPAREN RETURN IN EOF END COLON BAR ]
##
## The known suffix of the stack is as follows:
## REC obj RETURN VAR DOT obj BAR ZERO DARROW obj BAR SUCC VAR COMMA VAR DARROW obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: INT SUCC
##
## Ends in an error in state: 54.
##
## prog -> obj . COLON obj EOF [ # ]
##
## The known suffix of the stack is as follows:
## obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: INT COLON RPAREN
##
## Ends in an error in state: 55.
##
## prog -> obj COLON . obj EOF [ # ]
##
## The known suffix of the stack is as follows:
## obj COLON
##

<YOUR SYNTAX ERROR MESSAGE HERE>

prog: INT COLON INT SUCC
##
## Ends in an error in state: 56.
##
## prog -> obj COLON obj . EOF [ # ]
##
## The known suffix of the stack is as follows:
## obj COLON obj
##
## WARNING: This example involves spurious reductions.
## This implies that, although the LR(1) items shown above provide an
## accurate view of the past (what has been recognized so far), they
## may provide an INCOMPLETE view of the future (what was expected next).
## In state 24, spurious reduction of production obj -> app_obj
##

<YOUR SYNTAX ERROR MESSAGE HERE>

