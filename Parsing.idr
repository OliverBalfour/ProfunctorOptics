
module Parsing

Parser : Type -> Type
Parser a = List Char -> [(a, List Char)]

item : Parser Char
item = Parser (\x => case x of
  "" => []
  (c::cs) => [(c,cs)])

satisfy : (Char -> Bool) -> Parser Char
satisfy pred = item >>= (\c => if pred c then pure c else empty)

char : Char -> Parser Char
char c = satisfy (== c)

Functor Parser where
  fmap f (Parser p) = Parser (\cs =>
    map (\(x, cs') => (f x, cs')) (p cs))

digit : Parser Int
digit = fmap (read . unpack . (::[])) (satisfy isDigit)

Applicative Parser where
  pure x = Parser (\cs => [(x, cs)])
  f <*> a = Parser (\cs =>
    concat [parse (fmap fn a) cs' | (fn, cs') <- parse f cs])

Monad Parser where
  p >>= f = Parser (\cs =>
    concat [parse (f a) cs' | (a, cs') <- parse p cs])

Alternative Parser where
  empty = Parser (\_ => [])
  p <|> q = Parser (\cs =>
    let (p', q') = (parse p cs, parse q cs) in
    if length p' > 0 then p' else q')

space : Parser List Char
space = many (satisfy isSpace)

string : List Char -> Parser List Char
string "" = pure ""
string (c::cs) = (::) <$> char c <*> string cs

token : List Char -> Parser List Char
token symb = space *> string symb

mul : Parser (Int -> Int -> Int)
mul = token "*" *> pure (*) <|> token "/" *> pure div

add : Parser (Int -> Int -> Int)
add = token "+" *> pure (+) <|> token "-" *> pure (-)

pow : Parser (Int -> Int -> Int)
pow = (token "^" <|> token "**") *> pure (^)

integer : Parser Int
integer = let positive = fmap read (some (satisfy isDigit))
          in space *> unary_minus positive

unary_minus : Parser Int -> Parser Int
unary_minus p = char '-' *> fmap negate p <|> p

chainl1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = p >>= rest
  where rest a = ((op <*> pure a <*> p) >>= rest)  <|> pure a

chainr1 : Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = p >>= rest
  where rest a =  (op <*> pure a <*> (p >>= rest)) <|> pure a

expr = ((subexpr `chainr1` pow) `chainl1` mul) `chainl1` add
subexpr = token "(" *> expr <* token ")" <|> integer

repl : List Char -> List Char
repl cs = let results = parse expr cs in
  case results of
    [] => "Invalid expression"
    ((num, _)::_) => show num

interact : (List Char -> List Char) -> IO ()
interact f = putStrLn (pack $ f (fmap unpack getLine))

main : IO ()
main = interact (unlines' . map repl . lines')
