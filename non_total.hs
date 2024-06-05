-- A simple language with non-terminating loops
data Expr = Val Int | Add Expr Expr | Loop

-- The semantics for our language
eval :: Expr -> Int
eval (Val n) = n
eval (Add x y) = eval x + eval y
eval Loop = eval Loop

-- The compiler for our language that we want to _calculate_
-- comp :: Expr -> Code
-- We can change the signiture slightly, so we can do continuations
comp :: Expr -> Code -> Code
-- data Code = ...?

-- The target for our compiler: a stack based machine
type Stack = [Int]
exec :: Code -> Stack  -> Stack

-- We want to show the following property:
exec c (eval e : s) = exec (comp e c) s
-- As in: Executing a program on the stack which contains the result of evaulating an expression
--        is the same as compiling the expression (with the program as its continuation) and executing the compiled code on the stack