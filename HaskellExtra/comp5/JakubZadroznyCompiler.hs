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

type Stack = [Var]
type FS = Map FSym Int
type Code = [MInstr]

trueInstr = MConst (-1)
falseInstr = MConst 0

flookup :: FSym -> FS -> Int
flookup f fs = case Data.Map.lookup f fs of
    Nothing -> undefined
    Just x -> x

stackLookup :: Stack -> Var -> Code
stackLookup xs var = aux xs var 0
    where
        aux [] _ _ = []
        aux (x:xs) var n =
            if x == var then [MGetLocal n]
            else aux xs var (n + 1)

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

generate :: FS -> Stack -> Expr p -> State Int Code

generate _ stack (EVar _ var) = return $ stackLookup stack var
generate _ _ (EUnit _) = return []
generate _ _ (ENum _ n) = return $ [MConst n]
generate _ _ (EBool _ b) = return $ case b of
    True -> [trueInstr]
    False -> [falseInstr]

generate fs stack (EUnary _ op e) = do
    code <- generate fs stack e
    return $ code ++ [unopToInstr op]

generate fs stack (EBinary _ op e1 e2) = do
    code1 <- generate fs stack e1
    code2 <- generate fs ([] : stack) e2
    label1 <- newLabel
    label2 <- newLabel
    return $ code1 ++ [MPush] ++ code2 ++ compileOp op label1 label2

generate fs stack (ELet _ var e1 e2) = do
    code1 <- generate fs stack e1
    code2 <- generate fs (var : stack) e2
    return $ code1 ++ [MPush] ++ code2 ++ [MPopN 1]

generate fs stack (EIf _ e1 e2 e3) = do
    code1 <- generate fs stack e1
    code2 <- generate fs stack e3
    code3 <- generate fs stack e2
    label1 <- newLabel
    label2 <- newLabel
    return $ code1 ++ [MBranch MC_N label1] ++ code2 ++ [MJump label2, MLabel label1] ++ code3 ++ [MLabel label2]

generate fs stack (EPair _ e1 e2) = do
    code1 <- generate fs ([] : stack) e1
    code2 <- generate fs ([] : stack) e2
    return $ [MAlloc 2, MPush] ++ code1 ++ [MSet 0] ++ code2 ++ [MSet 1] ++ [MPopAcc]

generate fs stack (EFst _ e) = do
    code <- generate fs stack e
    return $ code ++ [MGet 0]
generate fs stack (ESnd _ e) = do
    code <- generate fs stack e
    return $ code ++ [MGet 1]

generate _ _ (ENil _ _) = do
    return $ [MAlloc 2, MPush, MConst 0, MSet 0, MSet 1, MPopAcc]

generate fs stack (ECons _ e1 e2) = do
    code1 <- generate fs ([] : stack) e1
    code2 <- generate fs ([] : stack) e2
    return $ [MAlloc 2, MPush] ++ code1 ++ [MSet 0] ++ code2 ++ [MSet 1] ++ [MPopAcc]

generate fs stack (EMatchL _ e eNil (x, xs, eCons)) = do
    code1 <- generate fs stack e
    code2 <- generate fs ([] : stack) eNil
    code3 <- generate fs (x : xs : [] : stack) eCons
    label1 <- newLabel
    label2 <- newLabel
    return $ code1 ++ [MPush, MGet 1] ++ [MBranch MC_NZ label1] ++ code2 ++ [MJump label2, MLabel label1] ++
        [MPush, MGetLocal 1, MGet 0, MPush] ++ code3 ++ [MPopN 2, MLabel label2, MPopN 1]

generate fs stack (EApp _ f e) = do
    code1 <- generate fs stack e
    return $ code1 ++ [MCall (flookup f fs)]

buildLabels :: [FunctionDef p] -> State Int FS
buildLabels [] = return empty
buildLabels (x:xs) = do
    labels <- buildLabels xs
    label <- newLabel
    return $ insert (funcName x) label labels

compileFunctions :: [FunctionDef p] -> FS -> State Int Code
compileFunctions [] _ = return []
compileFunctions (x:xs) fs = do
    code1 <- compileFunctions xs fs
    code2 <- generate fs [funcArg x] (funcBody x)
    return $ code1 ++ [MLabel (flookup (funcName x) fs), MPush] ++ code2 ++ [MPopN 1, MRet]

-- Funkcja kompilująca program
compile :: [FunctionDef p] -> [Var] -> Expr p -> [MInstr]
compile defs vars e = evalState code 0 where
    code = do
        fs <- buildLabels defs
        code1 <- compileFunctions defs fs
        code2 <- generate fs vars e
        return $ code2 ++ [MRet] ++ code1
