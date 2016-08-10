import System   
import FlatCurry.Files
import FlatCurry.Show

makeFlat :: [Prelude.Char] -> Prelude.IO ()
makeFlat s = do 
   flatProg  <- readFlatCurry s
   putStr (curroqc (showFlatProg flatProg))

curroqc :: String -> String
curroqc s = curroq s 0 0 0

curroq :: String -> Int -> Int -> Int -> String
curroq []      _  _ _      = []
curroq (c : r) cr crs cb = case c of
                         '(' |(isPrefixOf "Type" r) -> [c] ++ "Typec" ++ (curroq (drop 4 r) (cr + 1) crs cb)
                             | otherwise -> c : (curroq r (cr + 1) crs cb)
                         ')' -> c : (curroq r (cr - 1) crs cb)
                         '[' -> c : (curroq r 0 cr (cb + 1))
                         ']' -> c : (curroq r crs crs (cb - 1))
                         ',' | and [cr == 0, cb > 0] -> ';': (curroq r cr crs cb)
                             | otherwise ->  c : (curroq r cr crs cb)
                         _   -> c : (curroq r cr crs cb)

isPrefixOf :: [a] -> [a] -> Bool
isPrefixOf []    _  = True 
isPrefixOf (x:_) [] = False
isPrefixOf (x:xs) (y:ys) =  x == y && isPrefixOf xs ys

main :: Prelude.IO ()
main = do
   args <- getArgs
   makeFlat (head args)
