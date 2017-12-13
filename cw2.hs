--(App (App (Lam 3 (App (Var 4) (Var 3))) (Lam 3 ( App (Var 5) (Var 3)))) (Lam 6 (App (Var 3) (Var 4)))) (App (App (Lam 6 (App (Var 8) (Var 6))) (Lam 6 ( App (Var 10) (Var 6)))) (Lam 12 (App (Var 6) (Var 8))))
--Ex1
import Control.Applicative
import Data.Char

data Expr = App Expr Expr | Lam Int Expr | Var Int deriving (Show, Eq)

containsFromTo:: Int -> [(Int, Int)] -> Bool
containsFromTo _ [] = False
containsFromTo x ((from, to):fromTo) 
    | x == from = True
    | otherwise = containsFromTo x fromTo


getFromTo :: Int -> [(Int,Int)] -> Int
getFromTo x [] = x
getFromTo x ((from,to):fromTo) 
    | x == from = to
    |otherwise = getFromTo x fromTo

    
removeFromBindingList :: (Int, Int) -> [(Int, Int)] -> [(Int, Int)]
removeFromBindingList _ [] = []
removeFromBindingList (rb, t) ((from,to):bs)
    | rb == from = removeFromBindingList (rb,t) bs
    | otherwise = [(from, to)] ++ removeFromBindingList (rb,t) bs
    
putBinding :: (Int, Int) -> [(Int, Int)] -> [(Int, Int)]
putBinding nb bs = removeFromBindingList nb bs ++ [nb] 

transformVariables :: Expr ->  [(Int, Int)] -> Expr
transformVariables (App expr1 expr2) bindings = (App (transformVariables expr1 bindings) (transformVariables expr2  bindings))
transformVariables (Lam int expr)  bindings = (Lam (getFromTo int bindings) (transformVariables expr bindings))
transformVariables (Var int)  bindings = (Var (getFromTo int bindings))

getAFrom :: Expr  -> Int
getAFrom (App expr1 expr2)  = maximum([getAFrom expr1] ++ [getAFrom expr2])
getAFrom (Lam int expr)  = maximum ([int] ++ [getAFrom expr])
getAFrom (Var int)  = int

normalizeVariables :: Expr -> Int -> [(Int, Int)] -> Expr
normalizeVariables (App expr1 expr2) a bindings = (App result1 result2)
    where 
        result1 = normalizeVariables expr1 a bindings
        newA = (maximum ([(getAFrom result1) + 1] ++ [a]) )
        result2 = normalizeVariables expr2 newA bindings
normalizeVariables (Lam int expr) a bindings = (Lam a (normalizeVariables  expr (a+1) (putBinding (int, a) bindings)))
normalizeVariables (Var int) a bindings
    | containsFromTo int bindings == True = (Var (getFromTo int bindings))
    | otherwise = (Var (a))

containsBinding :: (Int, Int)  -> [(Int, Int)] -> Bool
containsBinding _ [] = False
containsBinding (x,y) ((bx,by):bs)
    | x == bx && y == by = True
    | otherwise = containsBinding (x,y) bs
    
getBindings :: Expr -> Expr -> [(Int, Int)] -> [(Int,Int)]
getBindings (App expr1 expr2) (App expr3 expr4) bindings= (getBindings expr1 expr3 bindings) ++ (getBindings expr2 expr4 bindings)
getBindings (Lam int1 expr1) (Lam int2 expr2) bindings
    | containsBinding (int1, int2) bindings == False = [(int1, int2)] ++ (getBindings expr1 expr2 bindings)
    | otherwise = getBindings expr1 expr2 bindings
getBindings (Var int1) (Var int2) bindings 
    | containsBinding (int1, int2) bindings == False = [(int1, int2)] 
    | otherwise = []

tester :: Expr -> Expr
tester expr = transformVariables (normalizeVariables expr 1 []) (getBindings (normalizeVariables expr 1 [])  expr [])
    
getVariablesLeft :: Expr -> [Int]
getVariablesLeft (App expr1 expr2) = getVariablesLeft (expr1) ++ getVariablesLeft (expr2)
getVariablesLeft (Lam int expr) = [int] ++ getVariablesLeft (expr)
getVariablesLeft (Var int) = []

getVariablesRight :: Expr -> [Int]
getVariablesRight (App expr1 expr2) = getVariablesRight (expr1) ++ getVariablesRight (expr2)
getVariablesRight (Lam int expr) = [] ++ getVariablesRight (expr)
getVariablesRight (Var int) = [int]

contains :: Int -> [Int] -> Bool
contains x [] = False
contains x (y:ys) 
    | x == y = True
    | otherwise = contains x ys              

listcontains:: [Int] -> [Int] -> [Int] 
listcontains [] _ = []
listcontains (x:xs) ys
    | contains x ys == False = [x] ++ listcontains xs ys
    | otherwise = listcontains xs ys

    
freeVariablesPure :: Expr -> [Int]
freeVariablesPure expr = listcontains (getVariablesRight expr) (getVariablesLeft expr) 



varToVar:: Int -> [(Int, Int)] -> Int
varToVar x [] = x
varToVar x ((from,to):bindings)
    | x == from = to
    | otherwise = varToVar x bindings
    
transfromVariablesToVariables ::[Int] -> [(Int, Int)] -> [Int]
transfromVariablesToVariables [] _ = []
transfromVariablesToVariables (x:xs) bindings = [varToVar x bindings] ++ transfromVariablesToVariables xs bindings
    
freeVariablesTrueValues :: Expr -> Expr -> [Int]
freeVariablesTrueValues normExpr expr = transfromVariablesToVariables freeVar bindings
    where
        bindings = getBindings normExpr expr []
        freeVar = freeVariablesPure normExpr
        
freeVariables :: Expr -> [Int]
freeVariables expr = freeVariablesTrueValues normExpr expr
    where normExpr = normalizeVariables expr 1 []

freeVariablesNormalized :: Expr -> [Int]
freeVariablesNormalized expr = freeVariables (normalizeVariables expr 1 [])    
    
--Ex2
renamePure:: Expr -> Int -> Int -> Expr
renamePure (App expr1 expr2)  x y = (App (renamePure expr1 x y) (renamePure expr2 x y))
renamePure (Lam int expr)   x y 
    | int == x = (Lam y    (renamePure expr  x y))
    | otherwise = (Lam int  (renamePure expr x y))
renamePure (Var int)  x y 
    | int == x = (Var y)
    | otherwise = (Var int)


renameNormalized :: Expr -> Expr -> Int -> Int -> [Int] -> Expr
renameNormalized (App expr1 expr2)  (App expr11 expr22) x y freeVar = (App (renameNormalized expr1 expr11 x y freeVar) (renameNormalized expr2 expr22 x y freeVar))
renameNormalized (Lam int1 expr1)   (Lam int2 expr2)   x y freeVar
    | int2 == x && contains int1 freeVar == False = (Lam y    (renameNormalized expr1 expr2 x y freeVar))
    | otherwise = (Lam int2 (renameNormalized expr1 expr2 x y freeVar))
renameNormalized (Var int1) (Var int2) x y freeVar
    | int2 == x && contains int1 freeVar == False = (Var y)
    | otherwise = (Var int2)

rename :: Expr -> Int -> Int -> Expr
rename expr var1 var2= renameNormalized (normalizeVariables expr 1 []) expr  var1 var2 freeVar
    where 
        freeVar = freeVariablesNormalized expr

--Ex3
isEmpty:: [Int] -> Bool
isEmpty [] = True
isEmpty x = False

removeFromList:: Int -> [Int] -> [Int] 
removeFromList _ [] = []
removeFromList x (y:ys) 
    | x == y = ys
    | otherwise = [y] ++ removeFromList x ys
    
equalLists :: [Int] -> [Int] -> Bool
equalLists [] [] = True
equalLists (x:xs) ys 
    | contains x ys == True = equalLists xs (removeFromList x ys)
    | otherwise = False


    
getNextValue :: [(Int, Int)] -> Int -> Int
getNextValue [] a = a
getNextValue ((_,x):xs) a 
    | x > a = getNextValue xs x
    | otherwise = getNextValue xs a
    
getFromToValues :: Expr -> [(Int, Int)] -> [(Int, Int)]
getFromToValues (App expr1 expr2) fromTo= (getFromToValues expr2 (getFromToValues expr1 fromTo)) ++ (getFromToValues expr1 fromTo)
getFromToValues (Lam int expr)  fromTo 
    | containsFromTo int fromTo == True = getFromToValues expr fromTo
    | otherwise = [(int, a+1)] ++ getFromToValues expr (fromTo ++ [(int, a+1)])
    where a = getNextValue(fromTo) 0
getFromToValues (Var int) fromTo
    | containsFromTo int fromTo == False =  [(int, a+1)]
    | otherwise = []
    where a = getNextValue(fromTo) 0 
    
changeVariables :: Expr -> [(Int, Int)] -> Expr
changeVariables (App expr1 expr2) fromTo = (App (changeVariables expr1 fromTo) (changeVariables expr2 fromTo))
changeVariables (Lam int expr) fromTo 
    | containsFromTo int fromTo == True = (Lam (getFromTo int fromTo) (changeVariables expr fromTo ))
    | otherwise = (Lam int (changeVariables expr fromTo ))
    
changeVariables (Var int) fromTo
    | containsFromTo int fromTo == True = (Var (getFromTo int fromTo))
    | otherwise = (Var int)

    
expressionComparator ::Expr -> Expr -> Bool
expressionComparator expr1 expr2 = (expr1 == expr2)
    
maximumHelper:: [Int] -> Int -> Int
maximumHelper [] a = a
maximumHelper (x:xs) a
    | x > a = maximumHelper xs x 
    | otherwise = maximumHelper xs a

myMaximum:: [Int] -> Int
myMaximum xs = maximumHelper xs 0   

alphaEquivalent1 :: Expr -> Expr
alphaEquivalent1 expr = normalizeVariables expr 1 []
    
alphaEquivalent :: Expr -> Expr -> Bool
alphaEquivalent expr1 expr2 
    | equalLists (freeVariablesTrueValues normExpr1 expr1) (freeVariablesTrueValues normExpr2 expr2) == False = False
    | otherwise = expressionComparator (alphaEquivalent1 expr1)  (alphaEquivalent1 expr2)
    where 
        normExpr1 = normalizeVariables expr1 1 []
        normExpr2 = normalizeVariables expr2 1 []

    
-- Ex4 

substitutionSimple :: Expr -> Int -> Expr -> Expr
substitutionSimple (App expr1 expr2) from to = (App (substitutionSimple expr1 from to) (substitutionSimple expr2 from to))
substitutionSimple (Lam int expr) from to 
    | int == from = (Lam int (substitutionSimple expr from to))
    | otherwise = (Lam int (substitutionSimple expr from to))
substitutionSimple (Var int) from to 
    | int == from = (to)
    | otherwise = (Var int)

verifyFreeVariables1 :: [Int] -> [Int] -> Bool    
verifyFreeVariables1 [] _ = True
verifyFreeVariables1 (x:xs) ys 
    | contains x ys == False = False
    | otherwise = verifyFreeVariables1 xs ys

getValueFromFreeVariables :: Int -> [(Int, Int)] -> Int   
getValueFromFreeVariables _ [] = 0 
getValueFromFreeVariables value ((from,to):bindings) 
    | value == from = to
    | otherwise = getValueFromFreeVariables value bindings
    
getValuesForFreeVariables:: [Int] -> [(Int, Int)] -> [Int]
getValuesForFreeVariables [] _ = []
getValuesForFreeVariables (x:xs) bindings = [(getValueFromFreeVariables x bindings)] ++ getValuesForFreeVariables xs bindings
    
verifyFreeVariables :: [Int] -> [(Int, Int)] ->[Int] -> [(Int, Int)] -> (Bool, [Int], [(Int,Int)], [Int], [(Int,Int)])
verifyFreeVariables fvlExp b1 fvlAfter b2 = ((verifyFreeVariables1 unbinded1 unbinded2), fvlExp, b1, fvlAfter, b2)
    where 
        unbinded1 = getValuesForFreeVariables fvlExp b1
        unbinded2 = getValuesForFreeVariables fvlAfter b2  
    
safeSubstitution :: Expr -> Expr -> [(Int, Int)] -> (Bool, [Int], [(Int,Int)], [Int], [(Int,Int)])
safeSubstitution expr1 expr2 bindings = verifyFreeVariables (freeVariablesPure expr2) bindings (freeVariablesPure newExprNorm) (getBindings newExprNorm newExpr [])
    where 
        newExpr = transformVariables expr1 bindings 
        newExprNorm = normalizeVariables newExpr 1 []
    


canSubstitute :: Expr -> Int -> Expr -> [(Int, Int)] -> (Bool, [Int], [(Int,Int)], [Int], [(Int,Int)])
canSubstitute expr from to bindings = safeSubstitution (substitutionSimple expr from to) to bindings



myOr :: Bool -> Bool -> Bool
myOr a b 
    | a == True = True
    | b == True = True
    | otherwise = False
    
normalizedHasRedex :: Expr -> [(Int, Int)] -> Bool
normalizedHasRedex (App (Lam int expr1) expr2) bindings
    | value == True = True
    | otherwise = myOr (normalizedHasRedex expr1 bindings)  (normalizedHasRedex expr2 bindings)
    where (value,q,w,e,r) = canSubstitute expr1 int expr2 bindings
    
normalizedHasRedex (App expr1 expr2) bindings =  myOr (normalizedHasRedex expr1 bindings)  (normalizedHasRedex expr2 bindings)
normalizedHasRedex (Lam int expr) bindings = normalizedHasRedex expr bindings
normalizedHasRedex (Var int) bindings = False
    
hasRedex :: Expr -> Bool
hasRedex (App (Lam int expr1) expr2) = True
hasRedex (App expr1 expr2) =  myOr (hasRedex expr1)  (hasRedex expr2)
hasRedex (Lam int expr) = hasRedex expr
hasRedex (Var int)  = False

--hasRedex expr = normalizedHasRedex normExpr (getBindings normExpr expr [])
   -- where normExpr  = normalizeVariables expr 1 []

--hasRedex (Lam 1 (App (Lam 2 (App (Var 2) (Var 2))) (Var 3)))
-- Ex5

addToListUnique :: Int -> [Int] -> [Int]
addToListUnique toAdd list 
    | contains toAdd list == True = list
    | otherwise = list ++ [toAdd]
    
mergeLists :: [Int] -> [Int] -> [Int]
mergeLists [] l = l
mergeLists (x:xs) l 
    | contains x l == True = mergeLists xs l
    | otherwise = mergeLists xs l ++ [x]
    
substituteWhileBounding:: Expr -> [(Int, Int)] -> [Int] -> [Int] ->  [Int] -> (Expr, [Int])
substituteWhileBounding (App expr1 expr2) bindings bounders freeVarTo conflicts = ((App resultExpr1 resultExpr2), newConflicts)
    where
        (resultExpr1, conflicts1) = substituteWhileBounding expr1 bindings bounders freeVarTo  conflicts
        (resultExpr2, conflicts2) = substituteWhileBounding expr2 bindings bounders freeVarTo  conflicts
        newConflicts = mergeLists conflicts1 conflicts2
        
substituteWhileBounding (Lam int expr) bindings bounders freeVarTo  conflicts = ((Lam int resultExpr), resultConflicts) 
    where (resultExpr, resultConflicts) = substituteWhileBounding expr bindings bounders freeVarTo  conflicts
   
substituteWhileBounding (Var int) bindings bounders freeVarTo conflicts
    | contains trueValue bounders == True && contains int freeVarTo == True  = ((Var int), (addToListUnique trueValue conflicts))
    | otherwise = ((Var int), conflicts)
    where
        trueValue = (getFromTo int bindings)

        
substitutionOnNormalized :: Expr -> Int -> Expr -> [(Int, Int)] -> [(Int, Int)] -> [Int] -> [Int] -> [Int] -> Int -> (Expr, [Int], Int)
substitutionOnNormalized (App expr1 expr2) from normTo bindingsExpr bindingsTo freeVarTo bounders freeVarExpr a = ((App result1 result2), newConflicts, a2) 
    where
        (result1, conflicts1, a1) = substitutionOnNormalized expr1 from normTo bindingsExpr bindingsTo freeVarTo bounders  freeVarExpr a
        (result2, conflicts2, a2) = substitutionOnNormalized expr2 from normTo bindingsExpr bindingsTo freeVarTo bounders  freeVarExpr a1
        newConflicts = mergeLists conflicts1 conflicts2
        
       
substitutionOnNormalized (Lam int expr) from normTo bindingsExpr bindingsTo freeVarTo bounders freeVarExpr a
    | contains trueValue conflicts == True = (Lam (newA+1) (renamePure resultExpr int (newA+1)), conflicts, (newA+1))  
    | otherwise = ((Lam trueValue resultExpr), conflicts , newA)
    where 
        trueValue = getFromTo int bindingsExpr
        newBounders = addToListUnique trueValue bounders
        (resultExpr, conflicts, newA) = substitutionOnNormalized expr from normTo bindingsExpr bindingsTo freeVarTo newBounders freeVarExpr a

substitutionOnNormalized (Var int) from normTo bindingsExpr bindingsTo freeVarTo bounders freeVarExpr newA
    | getFromTo int bindingsExpr == from && contains int freeVarExpr == True =  (trueExpr, conflicts, newA)
    | otherwise = ((Var trueValue), [], newA)
    where 
        trueValue = getFromTo int bindingsExpr
        (resultExpr, conflicts) = substituteWhileBounding normTo bindingsTo bounders freeVarTo [] 
        trueExpr = transformVariables normTo bindingsTo

substitute :: Expr -> Int -> Expr -> Expr
substitute expr from to = resultExpr
    where
        normExpr = normalizeVariables expr 1 []
        a = getAFrom normExpr
        normTo = normalizeVariables to (a+1) []
        bindingsExpr = getBindings normExpr expr []
        bindingsTo = getBindings normTo to []
        freeVarTo = freeVariablesPure normTo
        freeVarExpr = freeVariablesPure normExpr
        (resultExpr, conflicts, newA) = substitutionOnNormalized normExpr from normTo bindingsExpr bindingsTo freeVarTo [] freeVarExpr  a


substitution expr from to = (normExpr, a, normTo, bindingsExpr, bindingsTo, freeVarTo, freeVarExpr)
    where
        normExpr = normalizeVariables expr 1 []
        a = getAFrom normExpr
        normTo = normalizeVariables to (a+1) []
        bindingsExpr = getBindings normExpr expr []
        bindingsTo = getBindings normTo to []
        freeVarTo = freeVariablesPure normTo
        freeVarExpr = freeVariablesPure normExpr

--
toString :: Int -> String
toString x = "x" ++ show x


myPrint :: Expr -> Int -> Int -> String 

myPrint (App (App expr0 expr1) (App expr2 expr3)) last hasNext
    | last == 0 || hasNext == 0 = myPrint (App expr0 expr1) 0 1 ++"("++ myPrint (App expr2 expr3) 0 hasNext ++ ")"
    | otherwise = "(" ++ myPrint(App expr0 expr1) 0 1 ++ "(" ++ myPrint (App expr2 expr3) 0 hasNext++ ")" ++ ")"

myPrint (App (App expr0 expr1) expr2) last hasNext
    | last == 0 || hasNext == 0 =  myPrint (App expr0 expr1) 0 1 ++ myPrint expr2 0 hasNext
    | otherwise = "(" ++ myPrint (App expr0 expr1) 0 1 ++ myPrint expr2 0 hasNext ++ ")"
    
myPrint (App expr0 (App expr1 expr2)) last hasNext  
    | last == 0 || hasNext == 0 = myPrint expr0 0 1 ++ "(" ++ myPrint (App expr1 expr2) 0 hasNext ++ ")"
    | otherwise = "(" ++ myPrint expr0 0 1++ "(" ++ myPrint (App expr1 expr2) 0 hasNext ++ "))"
    
myPrint (App expr1 expr2) last hasNext
    | last == 0 || hasNext == 0 = myPrint expr1 0 1 ++ myPrint expr2 0 hasNext
    | otherwise = "(" ++ myPrint expr1 0 1 ++ myPrint expr2 0 hasNext ++ ")"
myPrint (Lam int (Lam int2 expr2)) last hasNext
    | last == 1 = toString int ++ myPrint (Lam int2 expr2) 1 hasNext
    | hasNext == 0 = "\\" ++ toString int ++ myPrint (Lam int2 expr2) 1 hasNext
    | otherwise =  "(\\" ++ toString int ++ myPrint (Lam int2 expr2) 1 hasNext ++ ")"
myPrint (Lam int expr) last hasNext
    | last == 1 = toString int ++ "->" ++ myPrint expr 1 hasNext
    | hasNext == 0 = "\\" ++toString int ++ "->" ++ myPrint expr 1 hasNext
    | otherwise = "(\\" ++ toString int ++ "->" ++ myPrint expr 1 hasNext ++ ")"
myPrint (Var int) last hasNext = toString int  
   
prettyPrint:: Expr -> String
prettyPrint expr = myPrint (normalizeVariables expr 1 []) (-1) 0

--prettyPrint (Lam 1 (Lam 2 (App (App (Var 1) (Var 3)) (App(Var 4) (Var 5) ))))
--prettyPrint (Lam 1 (App (Var 1) (Lam 1 (Var 1))))
--prettyPrint (Lam 1 (App (Lam 1 (Var 1)) (Var 1) ))
--prettyPrint (App (Lam 1 (Var 1)) (Lam 1 (Var 1)))

-- Basic definitions

--Parser Taken from Programming in Haskell by Graham Hutton \|/
    
newtype Parser a = P (String -> [(a,String)])

parse :: Parser a -> String -> [(a,String)]
parse (P p) inp = p inp

item :: Parser Char
item = P (\inp -> case inp of
                     []     -> []
                     (x:xs) -> [(x,xs)])

-- Sequencing parsers

instance Functor Parser where
   -- fmap :: (a -> b) -> Parser a -> Parser b
   fmap g p = P (\inp -> case parse p inp of
                            []        -> []
                            [(v,out)] -> [(g v, out)])

instance Applicative Parser where
   -- pure :: a -> Parser a
   pure v = P (\inp -> [(v,inp)])

   -- <*> :: Parser (a -> b) -> Parser a -> Parser b
   pg <*> px = P (\inp -> case parse pg inp of
                             []        -> []
                             [(g,out)] -> parse (fmap g px) out)

instance Monad Parser where
   -- (>>=) :: Parser a -> (a -> Parser b) -> Parser b
   p >>= f = P (\inp -> case parse p inp of
                           []        -> []
                           [(v,out)] -> parse (f v) out)

-- Making choices

instance Alternative Parser where
   -- empty :: Parser a
   empty = P (\inp -> [])

   -- (<|>) :: Parser a -> Parser a -> Parser a
   p <|> q = P (\inp -> case parse p inp of
                           []        -> parse q inp
                           [(v,out)] -> [(v,out)])

-- Derived primitives

sat :: (Char -> Bool) -> Parser Char
sat p = do x <- item
           if p x then return x else empty

digit :: Parser Char
digit = sat isDigit

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

letter :: Parser Char
letter = sat isAlpha

alphanum :: Parser Char
alphanum = sat isAlphaNum

char :: Char -> Parser Char
char x = sat (== x)

string :: String -> Parser String
string []     = return []
string (x:xs) = do char x
                   string xs
                   return (x:xs)

ident :: Parser String
ident = do x  <- lower
           xs <- many alphanum
           return (x:xs)

nat :: Parser Int
nat = do xs <- some digit
         return (read xs)

int :: Parser Int
int = do char '-'
         n <- nat
         return (-n)
       <|> nat

-- Handling spacing

space :: Parser ()
space = do many (sat isSpace)
           return ()

token :: Parser a -> Parser a
token p = do space
             v <- p
             space
             return v

identifier :: Parser String
identifier = token ident

natural :: Parser Int
natural = token nat

integer :: Parser Int
integer = token int

symbol :: String -> Parser String
symbol xs = token (string xs)

--End of Parser Taken from Programming in Haskell by Graham Hutton /|\

data ExtExpr =
    ExtApp ExtExpr ExtExpr
    | ExtLam [Int] ExtExpr
    | ExtVar Int
    deriving (Show, Eq)


exprParsApp :: [ExtExpr] ->  ExtExpr 
exprParsApp exprList 
     | lenList == 1 = (head exprList)
     | lenList == 2 = (ExtApp (head exprList) (lastElem exprList))
     | lenList == 3 = (ExtApp (exprParsApp (headTail exprList)) (lastElem exprList))
    where lenList = listLength exprList
    
    
exprParseTerm :: Parser ExtExpr
exprParseTerm =  do result <- many exprPars
                    let newResult = exprParsApp result
                    return (newResult)

exprParants :: Parser ExtExpr
exprParants = do symbol "("
                 result <-  exprParseTerm  

                 symbol ")"
                 return ( result) 
                
   
exprPars :: Parser ExtExpr   
exprPars = exprParants <|> exprParsLam <|> exprParsVar



exprParseApp :: Parser ExtExpr
exprParseApp = do resultExpr1 <- exprPars
                  resultExpr2 <- exprPars
                  return (ExtApp resultExpr1 resultExpr2)

headTail:: (Eq a)=>[a] -> [a]
headTail (x:xs)
    | xs == []   = []
    | otherwise = [x] ++ headTail xs
    
lastElem :: (Eq a) => [a] -> a
lastElem (x:xs) 
    | xs == [] = x
    | otherwise = lastElem xs
                  
parseTransformVariables :: [Int] -> ExtExpr
parseTransformVariables list
    | listLength list == 0 = (ExtVar (-1))
    | listLength list == 1 = (ExtVar (head list))
    | listLength list == 2 = (ExtApp (ExtVar (head list)) (ExtVar (head (tail list))))
    | otherwise = (ExtApp (parseTransformVariables (headTail list)) (ExtVar (lastElem list)))
    
                  
exprParsVar :: Parser ExtExpr
exprParsVar = do resultVars <- varsPars
                 return (parseTransformVariables resultVars)
 
exprParsLam :: Parser ExtExpr    
exprParsLam = do  symbol "\\"
                  resultVars <- varsPars
                  symbol "->"
                  resultExpr <- exprParseTerm
                  return (ExtLam resultVars (resultExpr))


varsPars :: Parser [Int]
varsPars = do resultExpr <- some varPars
              return resultExpr

varPars :: Parser Int
varPars = do symbol "x"
             xs <- digitsPars
             let result = formNumber xs
             return result

listLength:: [a] -> Int
listLength [] = 0
listLength (x:xs) = listLength xs + 1
             
formNumber' :: [Int] -> Int -> Int
formNumber' [] _ = 0
formNumber' _ 0 = 0
formNumber' (part:parts) multiplier = (formNumber' parts (multiplier `div` 10)) + (part * multiplier)

formNumber:: [Int] -> Int
formNumber parts = formNumber' parts multiplier
    where multiplier = (10 ^ (listLength parts - 1) ) 
    
digitsPars :: Parser [Int]
digitsPars = do xs <- some digitPars
                return xs
            
digitPars :: Parser Int
digitPars = do {x <- token (sat isDigit); return (ord x - ord '0')}

parseDigit :: String -> [(Int, String)]
parseDigit s = parse digitPars s

parseVars :: String -> [([Int], String)]
parseVars s = parse varsPars s

parseVar :: String -> [(Int, String)]
parseVar s = parse varPars s

parseDigits :: String -> [([Int], String)]
parseDigits s = parse digitsPars s

parseLam :: String -> Maybe ExtExpr
parseLam s = case (parseLam2 s) of
                    [(n,[])] -> Just n
                    [(_,out)] -> Nothing
                    [] -> Nothing
                    

parseLam2 :: String -> [(ExtExpr , String)]
parseLam2 s = a
    where a = parse exprParseTerm s     

    
parse' :: Parser a -> String -> [(a,String)]
parse' (P p) inp = p inp 

simplePrint :: String
simplePrint = "\\"


-- 

data ExprCL = AppCL ExprCL ExprCL | K | S | VarCL Int deriving (Show)


xFreeIn :: Int -> Expr -> Bool
xFreeIn x expr = contains x freeVar
    where freeVar = freeVariables expr

    
myTranslate :: Expr -> Expr
--1
myTranslate (Var int) = Var int
--2
myTranslate (App expr1 expr2) = (App (myTranslate expr1) (myTranslate expr2))
--3
myTranslate (Lam int expr)
    | xFreeIn int expr == False = (App (Var (-2)) (myTranslate expr))
--4
myTranslate (Lam int (Var int2)) 
    | int == int2 = (App (App (Var (-1)) (Var (-2))) (Var(-2)))
--5    
myTranslate (Lam int (Lam int2 expr))
    | xFreeIn int expr == True =  (myTranslate (Lam int (myTranslate (Lam int2 expr)))) 
--6    
myTranslate (Lam int (App expr1 expr2))
    | xFreeIn int expr1 == True || xFreeIn int expr2 == True = (App (App (Var (-1)) (myTranslate (Lam int expr1))) (myTranslate (Lam int expr2)))
    

    
tranformExpr :: Expr -> ExprCL
tranformExpr (App expr1 expr2) = (AppCL (tranformExpr expr1) (tranformExpr expr2))
tranformExpr (Var int) 
    | int == -1 = S
    | int == -2 = K
    | otherwise = (VarCL int)


translate :: Expr -> ExprCL
translate expr = tranformExpr (myTranslate expr)

