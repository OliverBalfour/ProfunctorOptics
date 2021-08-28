
module Main

import System.File

-- %default total

-- postulate whyNot : 5 = 6


-- trace : Show a => a -> a
-- trace x = snd (unsafePerformIO x, x)

main : IO ()
main = do
    filename <- getLine
    file <- readFile filename
    case file of
        Right content => putStr content
        Left error => print error

-- postulate trustMe : a -> b

-- oops : 1 = 2
-- oops = trustMe

total
lengthVect : {n : Nat} -> (xs : Vect n a) -> length xs = n
lengthVect [] = Refl
lengthVect (x::xs) =
  let iH = lengthVect xs
  in rewrite iH in Refl

total
proof2 : (xs : Vect (S n) a) -> length (tail xs) = n
proof2 [] impossible  -- the patterns never match
proof2 (x :: xs) = lengthVect
--   let inductiveHypothesis = proof2  -- Conor McBride calls this a shed
--   -- now iH shows up in the context, that's why sheds are useful
--   in lengthVect
--   -- we can't use induction because this proof doesn't have a base case
