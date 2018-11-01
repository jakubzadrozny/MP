-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko} gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module JakubZadrozny (typecheck, eval) where

-- Importujemy moduły z definicją języka oraz typami potrzebnymi w zadaniu
import AST
import DataTypes
import Data.Map

newtype Env a = Env (Map Var a)
data Err p = Err p String
type TypeChk p = Either (Err p) Type

data OpType = Arithmetic | Comparative | Boolean

empty_env :: Env a
empty_env = Env empty

init_env :: [(Var, a)] -> Env a
init_env = Env . fromList

extend_env :: Env a -> Var -> a -> Env a
extend_env (Env env) key val = Env (insert key val env)

env_lookup :: Env a -> Var -> Maybe a
env_lookup (Env env) = flip Data.Map.lookup env

pfail :: p -> String -> TypeChk p
pfail p msg = Left $ Err p msg

pfail' :: Err p -> TypeChk p
pfail' err = Left err

operator_type :: BinaryOperator -> OpType
operator_type op
    | elem op [BAnd, BOr] = Boolean
    | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] = Comparative
    | otherwise = Arithmetic

check_type1 :: [FunctionDef p] -> Env Type -> (Expr p, Type) -> (Type, Err p) -> TypeChk p
check_type1 fs env (expr, t1) (t2, err) = do
    t1' <- infer_type fs env expr
    if t1' == t1 then return t2
    else pfail' err

check_type2 :: [FunctionDef p] -> Env Type -> (Expr p, Type) -> (Expr p, Type) -> (Type, Err p) -> TypeChk p
check_type2 fs env (e1, t1) (e2, t2) (t, err) = do
    t1' <- infer_type fs env e1
    if t1' /= t1 then pfail' err
    else check_type1 fs env (e2, t2) (t, err)

flookup :: FSym -> [FunctionDef p] -> Maybe (Type, Type)
flookup _ [] = Nothing
flookup f (def:defs) =
    if funcName def == f
        then Just (funcArgType def, funcResType def)
        else flookup f defs

ftypecheck :: [FunctionDef p] -> [FunctionDef p] -> TypeChk p
ftypecheck _ [] = return TInt
ftypecheck gs (f:fs) = do
    t <- infer_type gs env (funcBody f)
    if t == funcResType f then ftypecheck gs fs
    else pfail (funcPos f) "function does not have the declared type"
    where env = extend_env empty_env (funcArg f) (funcArgType f)

infer_type :: [FunctionDef p] -> Env Type -> Expr p -> TypeChk p

infer_type _ _ (ENum _ _) = return TInt
infer_type _ _ (EBool _ _) = return TBool
infer_type _ _ (EUnit _) = return TUnit
infer_type _ _ (ENil p t) = case t of
    TList _ -> return t
    otherwise -> pfail p "empty list of non-list type"

infer_type _ env (EVar pos var) =
    case env_lookup env var of
        Nothing -> pfail pos "undefined variable found"
        Just t -> return t

infer_type fs env (EUnary pos op e) = case op of
    UNeg -> check_type1 fs env (e, TInt) (TInt, Err pos "argument of negation should be an integers")
    UNot -> check_type1 fs env (e, TBool) (TBool, Err pos "argument of not should be a boolean")

infer_type fs env (EBinary pos op e1 e2) = case operator_type op of
    Arithmetic -> check_type2 fs env (e1, TInt) (e2, TInt) (TInt, Err pos "both arguments of an arithemtic operator should be integers")
    Boolean -> check_type2 fs env (e1, TBool) (e2, TBool) (TBool, Err pos "both arguments of a boolean operator should be boolean")
    Comparative -> check_type2 fs env (e1, TInt) (e2, TInt) (TBool, Err pos "both arguments of a comparison should be integers")

infer_type fs env (ELet _ var e1 e2) = do
    t <- infer_type fs env e1
    let env1 = extend_env env var t in infer_type fs env1 e2

infer_type fs env (EIf pos e1 e2 e3) = do
    t1 <- infer_type fs env e1
    t2 <- infer_type fs env e2
    t3 <- infer_type fs env e3
    if t1 /= TBool then pfail pos "first expression of an if statement should be a boolean"
    else if t2 /= t3
        then pfail pos "second and third expressions of an if statement should be of the same type"
        else return t2

infer_type fs env (EPair pos e1 e2) = do
    t1 <- infer_type fs env e1
    t2 <- infer_type fs env e2
    return (TPair t1 t2)

infer_type fs env (EFst pos e) = do
    t <- infer_type fs env e
    case t of
        TPair t1 _ -> return t1
        otherwise -> pfail pos "projecting non-pair type"

infer_type fs env (ESnd pos e) = do
    t <- infer_type fs env e
    case t of
        TPair _ t2 -> return t2
        otherwise -> pfail pos "projecting non-pair type"

infer_type fs env (EApp pos f e) = case flookup f fs of
    Nothing -> pfail pos "applied function does not exist"
    Just (tArg, tRes) -> check_type1 fs env (e, tArg) (tRes, Err pos "cannot apply function to argument of such type")

infer_type fs env (ECons pos e1 e2) = do
    t <- infer_type fs env e1
    check_type1 fs env (e2, TList t) (TList t, Err pos "constructing list of different types")

infer_type fs env (EMatchL pos e e1 (x1, x2, e2)) = do
    t1 <- infer_type fs env e
    t2 <- infer_type fs env e1
    case t1 of
        TList t -> let env1 = extend_env env x1 t in let env2 = extend_env env1 x2 t1 in
            check_type1 fs env2 (e2, t2) (t2, Err pos "both cases of match should be of same type")
        otherwise -> pfail pos "match expression done on non-list type"

-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck fs vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck fs vars e = case t of
    Right _ -> Ok
    Left (Err pos msg) -> Error pos msg
    where
        env = init_env var_types
        var_types = zip vars ints
        ints = TInt : ints
        t = do
            ftypecheck fs fs
            check_type1 fs env (e, TInt) (TInt, Err (getData e) "program output should be an int")

-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval fs input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że definicje funckcji fs oraz wyrażenie e są dobrze
-- typowane, tzn. typecheck fs (map fst input) e = Ok

data Value =
    VInt Integer |
    VBool Bool |
    VUnit |
    VPair Value Value |
    VList [Value]

data Funcs = Funcs (Map FSym (Value -> Maybe Value))

fromInt (VInt x) = x
fromBool (VBool x) = x
fromPair (VPair x y) = (x, y)
fromListVal (VList x) = x

to_func :: Funcs -> FunctionDef p -> (FSym, Value -> Maybe Value)
to_func funcs f = (funcName f, g)
    where g x = let env = extend_env empty_env (funcArg f) x in count funcs env (funcBody f)

fs_lookup :: Funcs -> FSym -> Maybe (Value -> Maybe Value)
fs_lookup (Funcs fs) = flip Data.Map.lookup fs

init_fs :: [FunctionDef p] -> Funcs
init_fs defs = fs
    where fs = Funcs . fromList $ Prelude.map (to_func fs) defs

count_op' :: (Value -> a) -> (b -> Value) -> (a -> b) -> Value -> Value
count_op' unwrap wrap f = wrap . f . unwrap

count_op :: (Value -> a) -> (b -> Value) -> (a -> a -> b) -> Value -> Value -> Value
count_op unwrap wrap f x y = wrap $ f (unwrap x) (unwrap y)

count :: Funcs -> Env Value -> Expr p -> Maybe Value

count _ _ (ENum _ n) = return $ VInt n
count _ _ (EBool _ b) = return $ VBool b
count _ _ (EUnit _) = return VUnit
count _ _ (ENil _ _) = return $ VList []
count _ env (EVar _ var) = env_lookup env var

count fs env (EUnary _ op e) = do
    x <- count fs env e
    case op of
        UNot -> return $ count_op' fromBool VBool not x
        UNeg -> return $ count_op' fromInt VInt (*(-1)) x

count fs env (EBinary _ op e1 e2) = do
    x <- count fs env e1
    y <- count fs env e2
    case op of
        BAnd -> return $ count_op fromBool VBool (&&) x y
        BOr -> return $ count_op fromBool VBool (||) x y
        BEq -> return $ count_op fromInt VBool (==) x y
        BNeq -> return $ count_op fromInt VBool (/=) x y
        BLt -> return $ count_op fromInt VBool (<) x y
        BGt -> return $ count_op fromInt VBool (>) x y
        BLe -> return $ count_op fromInt VBool (<=) x y
        BGe -> return $ count_op fromInt VBool (>=) x y
        BAdd -> return $ count_op fromInt VInt (+) x y
        BSub -> return $ count_op fromInt VInt (-) x y
        BMul -> return $ count_op fromInt VInt (*) x y
        BDiv -> if fromInt y == 0 then fail "" else return $ count_op fromInt VInt div x y
        BMod -> if fromInt y == 0 then fail "" else return $ count_op fromInt VInt mod x y

count fs env (ELet _ var e1 e2) = do
    x <- count fs env e1
    let env1 = extend_env env var x in count fs env1 e2

count fs env (EIf _ e1 e2 e3) = do
    x <- count fs env e1
    if fromBool x == True then count fs env e2
    else count fs env e3

count fs env (EPair _ e1 e2) = do
    x <- count fs env e1
    y <- count fs env e2
    return $ VPair x y

count fs env (EFst _ e) = do
    x <- count fs env e
    return . fst . fromPair $ x

count fs env (ESnd _ e) = do
    x <- count fs env e
    return . snd . fromPair $ x

count fs env (ECons _ e1 e2) = do
    x <- count fs env e1
    xs <- count fs env e2
    return $ count_op' fromListVal VList (x:) xs

count fs env (EMatchL _ e1 e2 (v1, v2, e3)) = do
    val <- count fs env e1
    let xss = fromListVal val in
        case xss of
            [] -> count fs env e2
            (x:xs) -> let env1 = extend_env env v1 x in
                let env2 = extend_env env1 v2 (VList xs) in count fs env2 e3

count fs env (EApp _ f e) = do
    x <- count fs env e
    g <- fs_lookup fs f
    g x

eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval funcs vars e = case count fs env e of
    Nothing -> RuntimeError
    Just (VInt n) -> Value n
    where
        fs = init_fs funcs
        vs = Prelude.map (applys VInt) vars
        env = init_env vs
        applys f (a, b) = (a, f b)
