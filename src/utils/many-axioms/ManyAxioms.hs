
header :: IO ()
header =
  putStrLn $
    "-- This file was automatically generated.\n\n"
    ++ "module ManyAxioms where\n\n"
    ++ "postulate\n"
    ++ "  D : Set\n"
    ++ "  _≡_ : D -> D -> Set\n"

variable :: Int -> IO ()
variable n = do
  let ai :: String
      ai = 'a' : show n
  putStrLn $ "postulate " ++ ai ++ " : D"

axiom :: Int -> IO ()
axiom n = do
  let ai :: String
      ai = 'a' : show n

      aj :: String
      aj = 'a' : show (n + 1)

      ax :: String
      ax = "ax" ++ show n

  putStrLn $ "postulate " ++ ax ++ " : " ++ ai ++ " ≡ " ++ aj
  putStrLn $ "{-# ATP axiom " ++ ax ++ " #-}\n"

footer :: Int -> IO ()
footer n = do
  let ai :: String
      ai = 'a' : show (n - 1)

      aj :: String
      aj = 'a' : show n

  putStrLn $ "postulate foo : " ++ ai ++ " ≡ " ++ aj
  putStrLn "{-# ATP prove foo #-}"

totalVar :: Int
totalVar = 1000

main :: IO ()
main = do
  header
  mapM_ variable [1..totalVar]
  putStr "\n"
  mapM_ axiom    [1..(totalVar -1)]
  footer totalVar
