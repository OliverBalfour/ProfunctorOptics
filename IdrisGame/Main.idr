
module Main

flushTerminal : IO ()
flushTerminal = putStr (pack (replicate 100 "\n"))

main : IO ()
main = flushTerminal
