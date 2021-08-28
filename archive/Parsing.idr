
module Parsing

Parser : Type -> Type
Parser a = List Char -> List (a, List Char)

Functor Parser where
  map f p = \cs =>
    map (\(x, cs') => (f x, cs')) (p cs)

Applicative Parser where
  pure x = \cs => [(x, cs)]
  f <*> a = \cs =>
    concat [(map {f=Parser} fn a) cs' | (fn, cs') <- f cs]

Monad Parser where
  p >>= f = \cs =>
    concat [(f a) cs' | (a, cs') <- p cs]

Alternative Parser where
  empty = \_ => []
  p <|> q = \cs =>
    let (p', q') = (p cs, q cs) in
    if length p' > 0 then p' else q'

item : Parser Char
item = \x => case x of
  [] => []
  (c::cs) => [(c,cs)]

satisfy : (Char -> Bool) -> Parser Char
satisfy pred = (>>=) {m=Parser} item
  (\c => if pred c then pure {f=Parser} c else empty {f=Parser})

char : Char -> Parser Char
char c = satisfy (== c)

digit : Parser Int
digit = map (read . unpack . (::[])) (satisfy isDigit)

space : Parser (List Char)
space = many (satisfy isSpace)

string : List Char -> Parser (List Char)
string [] = pure []
string (c::cs) = (::) <$> char c <*> string cs

token : List Char -> Parser (List Char)
token symb = space *> string symb

mul : Parser (Int -> Int -> Int)
mul = token "*" *> pure (*) <|> token "/" *> pure div

add : Parser (Int -> Int -> Int)
add = token "+" *> pure (+) <|> token "-" *> pure (-)

pow : Parser (Int -> Int -> Int)
pow = (token "^" <|> token "**") *> pure (^)

integer : Parser Int
integer = let positive = map read (some (satisfy isDigit))
          in space *> unary_minus positive

unary_minus : Parser Int -> Parser Int
unary_minus p = char '-' *> map negate p <|> p

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = p >>= rest
  where rest a = ((op <*> pure a <*> p) >>= rest)  <|> pure a

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = p >>= rest
  where rest a =  (op <*> pure a <*> (p >>= rest)) <|> pure a

expr = ((subexpr `chainr1` pow) `chainl1` mul) `chainl1` add
subexpr = token "(" *> expr <* token ")" <|> integer

repl : List Char -> List Char
repl cs = let results = expr cs in
  case results of
    [] => "Invalid expression"
    ((num, _)::_) => show num

interact : (List Char -> List Char) -> IO ()
interact f = putStrLn (pack $ f (map unpack getLine))

main : IO ()
main = interact (unlines' . map repl . lines')
