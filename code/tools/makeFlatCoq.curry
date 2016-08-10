import System   
import FlatCurry.Files
import FlatCurry.Show
import Char

makeFlat :: [Prelude.Char] -> Prelude.IO ()
makeFlat s = do 
   flatProg  <- readFlatCurry s
   putStr (curroqc (showFlatProg flatProg))

curroqc :: String -> String
curroqc s = curroq s 0 [] 0

curroq :: String -> Int -> [Int] -> Int -> String
curroq []      cr crs cb = (show cr) ++ ['|'] ++ (show crs) ++ ['|'] ++ (show cb)
curroq (c : r) cr crs cb = case c of
                         '(' |(isPrefixOf "Type" r) -> [c] ++ "Typec" ++ (curroq (drop 4 r) (cr + 1) crs cb)
                             | otherwise -> c : (curroq r (cr + 1) crs cb)
                         ')' -> c : (curroq r (cr - 1) crs cb)
                         '[' -> c : (curroq r 0 (cr : crs) (cb + 1))
                         ']' -> c : (curroq r (head crs) (drop 1 crs) (cb - 1))
                         ',' | and [cr == 0, cb > 0] -> ';': (curroq r cr crs cb)
                             | otherwise ->  c : (curroq r cr crs cb)
                         '\''-> '"' : (curroq r cr crs cb)
                         --'"' -> [c] ++ (textUntilQuote r) ++ (curroq (drop (length (textUntilQuote r)) r) cr crs cb)
                         _   -> c : (curroq r cr crs cb)

isPrefixOf :: [a] -> [a] -> Bool
isPrefixOf []    _  = True 
isPrefixOf (x:_) [] = False
isPrefixOf (x:xs) (y:ys) =  x == y && isPrefixOf xs ys

--textUntilQuote :: String -> String
--textUntilQuote [] = ""
--textUntilQuote [c] = [c]
--textUntilQuote (c : (c' : s)) | c == '"' = [c]
--                              | c == '\\' = "asd"
--                              | and [c' == '"', c == '\\'] = ['\'', '"']
--                              | and [c' == '"', not (c == '\\')] = [c, c']
--                              | otherwise = c : (textUntilQuote (c' : s))

main :: Prelude.IO ()
main = do
   args <- getArgs
   makeFlat (head args)
