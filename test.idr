module Main

-- main : IO ()
-- main = return ()

foo : Int -> Type
foo 0 = Bool
foo _ = String

bar : (x : Int) -> foo x
bar n = if n == 0 then True else ""
