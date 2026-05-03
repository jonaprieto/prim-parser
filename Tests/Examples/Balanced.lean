import Examples.Balanced
import Tests.Basic

open Parser Balanced

#guard group.runResult? (toText "()") == some ()
#guard group.runResult? (toText "(())") == some ()
#guard group.runResult? (toText "(()())") == some ()
#guard group.runResult? (toText "((()))") == some ()

#guard group.runResult? (toText "") == none
#guard group.runResult? (toText "(") == none
#guard group.runResult? (toText "(()") == none
#guard group.runResult? (toText ")(") == none

#guard balanced.runResult? (toText "") == some []
#guard balanced.runResult? (toText "()") == some [()]
#guard balanced.runResult? (toText "()()") == some [(), ()]
#guard balanced.runResult? (toText "(())()") == some [(), ()]
