
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
