-- Jakub Zadrozny
-- MP 2017 - Zadanie dodatkowe na pracownie z Haskella
-- Wersja dla pracowni 6

{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko}Compiler gdzie
-- za {Imie} i {Nazwisko} należy podstawić odpowiednio swoje imię
-- i nazwisko zaczynające się wielką literą oraz bez znaków diakrytycznych.
module JakubZadroznyCompiler(compile) where

import AST
import MacroAsm
import Control.Monad.State
import Data.Map
import Data.List

type Stack = [Var]
type Code = [MInstr]

generate :: Stack -> Expr p -> State Int (Code, Code)

generate _ (EUnit _) = return ([], [])
generate _ (ENum _ n) = return $ ([MConst n], [])
generate _ (EBool _ b) = return $ (case b of
    True -> [trueInstr]
    False -> [falseInstr], [])

generate _ (ENil _ _) = do
        return $ ([MAlloc 2, MPush, MConst 0, MSet 0, MSet 1, MPopAcc], [])

generate st (EVar _ var) = return $ (varLookup st var, [])

generate st (EUnary _ op e) = do
    (code, rest)<- generate st e
    return $ (code ++ [unopToInstr op], rest)

generate st (EBinary _ op e1 e2) = do
    (code1, rest1) <- generate st e1
    (code2, rest2) <- generate ([] : st) e2
    label1 <- newLabel
    label2 <- newLabel
    return $ (code1 ++ [MPush] ++ code2 ++ compileOp op label1 label2, rest1 ++ rest2)

generate st (ELet _ var e1 e2) = do
    (code1, rest1) <- generate st e1
    (code2, rest2) <- generate (var : st) e2
    return $ (code1 ++ [MPush] ++ code2 ++ [MPopN 1], rest1 ++ rest2)

generate st (EIf _ e1 e2 e3) = do
    (code1, rest1) <- generate st e1
    (code2, rest2) <- generate st e3
    (code3, rest3) <- generate st e2
    label1 <- newLabel
    label2 <- newLabel
    return $ (code1 ++ [MBranch MC_N label1] ++ code2 ++ [MJump label2, MLabel label1] ++ code3 ++ [MLabel label2], rest1 ++ rest2 ++ rest3)

generate st (EPair _ e1 e2) = do
    (code1, rest1) <- generate ([] : st) e1
    (code2, rest2) <- generate ([] : st) e2
    return $ ([MAlloc 2, MPush] ++ code1 ++ [MSet 0] ++ code2 ++ [MSet 1] ++ [MPopAcc], rest1 ++ rest2)

generate st (EFst _ e) = do
    (code, rest) <- generate st e
    return $ (code ++ [MGet 0], rest)
generate st (ESnd _ e) = do
    (code, rest) <- generate st e
    return $ (code ++ [MGet 1], rest)

generate st (ECons _ e1 e2) = do
    (code1, rest1) <- generate ([] : st) e1
    (code2, rest2) <- generate ([] : st) e2
    return $ ([MAlloc 2, MPush] ++ code1 ++ [MSet 0] ++ code2 ++ [MSet 1] ++ [MPopAcc], rest1 ++ rest2)

generate st (EMatchL _ e eNil (x, xs, eCons)) = do
    (code1, rest1) <- generate st e
    (code2, rest2) <- generate ([] : st) eNil
    (code3, rest3) <- generate (xs : x : [] : st) eCons
    label1 <- newLabel
    label2 <- newLabel
    return $ (code1 ++ [MPush, MGet 1] ++ [MBranch MC_NZ label1] ++ code2 ++ [MJump label2, MLabel label1] ++
        [MGetLocal 0, MGet 0, MPush, MGetLocal 1, MGet 1, MPush] ++ code3 ++ [MPopN 2, MLabel label2, MPopN 1], rest1 ++ rest2 ++ rest3)

generate st (EFn _ arg _ e) = do
    code1 <- createClosure ([] : st) vars
    label <- newLabel
    (code2, rest) <- generate (arg : "__fcall" : vars) e
    return $ ([MAlloc (length vars + 1), MPush, MGetLabel label, MSet 0] ++ code1 ++ [MPopAcc],
              rest ++ [MLabel label] ++ code2 ++ [MPopN 2, MRet])
    where vars = getVars [arg] e

generate st (EApp _ e1 e2) = do
    (code1, rest1) <- generate st e1
    (code2, rest2) <- generate ([] : st) e2
    return $ (code1 ++ [MPush] ++ code2 ++ [MPush, MGetLocal 1, MGet 0, MCallAcc], rest1 ++ rest2)

buildStack :: [FunctionDef p] -> State Int Code
buildStack fs = return $ aux fs
    where
        aux [] = []
        aux (x:xs) = let n = length (getVars [funcArg x] (funcBody x)) in [MAlloc (n + 1), MPush] ++ aux xs

compileFunctions :: [FunctionDef p] -> Stack -> State Int (Code, Code)
compileFunctions fs st = aux fs 0
    where
        aux :: [FunctionDef p] -> Int -> State Int (Code, Code)
        aux [] _ = return ([], [])
        aux (x:xs) n = do
            let vars = getVars [funcArg x] (funcBody x)
            code <- createClosure ([] : st) vars
            label <- newLabel
            (code1, rest1) <- generate (funcArg x : "__fcall" : vars) (funcBody x)
            (code2, rest2) <- aux xs (n + 1)
            return $ ([MGetLocal n, MPush, MGetLabel label, MSet 0] ++ code ++ [MPopN 1] ++ code2,
                      rest2 ++ rest1 ++ [MLabel label] ++ code1 ++ [MPopN 2, MRet])

genOpt :: Code -> Code
genOpt code = [MPush, MGetLocal 1] ++
  (if n > 0 then [MSetLocal (n + 1), MGetLocal 0, MSetLocal n, MPopN n, MGetLocal 1] else []) ++
  [MGet 0, MJumpAcc]
  where
      n = addPops code 0
      addPops [] n = n
      addPops ((MPopN k) : xs) n = addPops xs (n + k)

optimize :: Code -> Code
optimize code = aux1 code
  where
      aux1 [] = []
      aux1 ((MPush):(MGetLocal 1):(MGet 0):(MCallAcc):xs) = aux2 xs []
      aux1 (x:xs) = x : aux1 xs
      aux2 [] acc = acc
      aux2 (x:xs) acc = case x of
          MPopN _ -> aux2 xs (x : acc)
          MRet -> genOpt acc ++ aux1 xs
          otherwise -> [MPush, MGetLocal 1, MGet 0, MCallAcc] ++ acc ++ [x] ++ aux1 xs

-- Funkcja kompilująca program
compile :: [FunctionDef p] -> [Var] -> Expr p -> [MInstr]
compile fs vars e = optimize compiled where
    compiled = evalState code 0
    st = Prelude.map funcName fs
    n = length fs
    code = do
        code1 <- buildStack (reverse fs)
        (code2, rest2) <- compileFunctions fs st
        (code3, rest3) <- generate (st ++ vars) e
        return $ code1 ++ code2 ++ code3 ++ [MPopN n, MRet] ++ rest2 ++ rest3

trueInstr = MConst (-1)
falseInstr = MConst 0

createClosure :: Stack -> Stack -> State Int Code
createClosure st vars = return $ aux vars 0
    where
        aux [] _ = []
        aux (x:xs) n = varLookup st x ++ [MSet (n + 1)] ++ aux xs (n + 1)

varLookup :: Stack -> Var -> Code
varLookup st var = aux1 st 0
    where
        aux1 [] _ = []
        aux1 (x:xs) n =
            if x == var then [MGetLocal n]
            else if x == "__fcall" then [MGetLocal n] ++ aux2 xs 0
            else aux1 xs (n + 1)
        aux2 [] _ = []
        aux2 (x:xs) n =
            if x == var then [MGet (n + 1)]
            else aux2 xs (n + 1)

unopToInstr :: UnaryOperator -> MInstr
unopToInstr UNot = MNot
unopToInstr UNeg = MNeg

opToCond :: BinaryOperator -> MCondition
opToCond BEq  = MC_EQ
opToCond BNeq = MC_NE
opToCond BLt  = MC_LT
opToCond BGt  = MC_GT
opToCond BLe  = MC_LE
opToCond BGe  = MC_GE

compileOp :: BinaryOperator -> Int -> Int -> Code
compileOp BAnd _ _ = [MAnd]
compileOp BOr _ _  = [MOr]
compileOp BAdd _ _ = [MAdd]
compileOp BSub _ _ = [MSub]
compileOp BMul _ _ = [MMul]
compileOp BDiv _ _ = [MDiv]
compileOp BMod _ _ = [MMod]
compileOp op label1 label2 =
    [MBranch (opToCond op) label1, falseInstr, MJump label2, MLabel label1, trueInstr, MLabel label2]

newLabel :: State Int Int
newLabel = do
    s <- get
    put (s + 1)
    return s

getVariables, getVars :: Stack -> Expr p -> Stack

getVars st e = Data.List.nub (getVariables st e)

getVariables st (EVar _ var) =
    if var `elem` st then []
    else [var]

getVariables _ (ENum _ _) = []
getVariables _ (EBool _ _) = []
getVariables _ (EUnit _) = []
getVariables _ (ENil _ _) = []
getVariables st (EUnary _ _ e) = getVariables st e
getVariables st (EBinary _ _ e1 e2) = getVariables st e1 ++ getVariables st e2
getVariables st (ELet _ var e1 e2) = getVariables st e1 ++ getVariables (var : st) e2
getVariables st (EIf _ e1 e2 e3) = getVariables st e1 ++ getVariables st e2 ++ getVariables st e3
getVariables st (EFn _ arg _ e) = getVariables (arg : st) e
getVariables st (EApp _ e1 e2) = getVariables st e1 ++ getVariables st e2
getVariables st (EPair _ e1 e2) = getVariables st e1 ++ getVariables st e2
getVariables st (EFst _ e) = getVariables st e
getVariables st (ESnd _ e) = getVariables st e
getVariables st (ECons _ e1 e2) = getVariables st e1 ++ getVariables st e2
getVariables st (EMatchL _ e1 e2 (x1, x2, e3)) = getVariables st e1 ++ getVariables st e2 ++ getVariables (x1 : x2 : st) e3
