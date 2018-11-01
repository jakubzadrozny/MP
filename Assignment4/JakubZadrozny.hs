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

data Env a = Env (Map Var a) deriving Show
data OpType = Arithmetic | Comparative | Boolean
data Err p = Err p String deriving Show
instance Eq (Err p) where x == y = True

data Type = Int | Bool deriving (Eq, Show)

type Value = Either Integer Bool
type TypeChk p = Either Type (Err p)

fromRight :: Either a b -> b
fromRight (Right a) = a

fromLeft :: Either a b -> a
fromLeft (Left a) = a

empty_env :: Env a
empty_env = Env empty

init_env :: [(Var, a)] -> Env a
init_env = Env . fromList

extend_env :: Env a -> Var -> a -> Env a
extend_env (Env env) key val = Env (insert key val env)

env_lookup :: Env a -> Var -> Maybe a
env_lookup (Env env) = flip Data.Map.lookup env

-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
typecheck :: [Var] -> Expr p -> TypeCheckResult p
typecheck vars program =
    case infer_type env program of
        Left Int -> Ok
        Left Bool -> Error pos1 "output should be an int"
        Right (Err pos msg) -> Error pos msg
    where   env = init_env var_types
            var_types = zip vars ints
            ints = Int : ints
            pos1 = getData program

check_type1 :: Env Type -> Expr p -> Type -> Type -> Err p -> TypeChk p
check_type1 env e1 t1 t err =
    if actual == Left t1
        then Left t
        else case actual of
            Right _ -> actual
            otherwise -> Right err
    where actual = infer_type env e1

check_type2 :: Env Type -> Expr p -> Type -> Expr p -> Type -> Type -> Err p -> TypeChk p
check_type2 env e1 t1 e2 t2 t err =
    if types == (Left t1, Left t2)
        then Left t
        else case types of
            (Right _, _) -> fst types
            (_, Right _) -> snd types
            otherwise -> Right err
    where types = (infer_type env e1, infer_type env e2)

operator_type :: BinaryOperator -> OpType
operator_type op
    | elem op [BAnd, BOr] = Boolean
    | elem op [BEq, BNeq, BLt, BGt, BLe, BGe] = Comparative
    | otherwise = Arithmetic

infer_type :: Env Type -> Expr p -> TypeChk p

infer_type _ (ENum _ _) = Left Int
infer_type _ (EBool _ _) = Left Bool

infer_type env (EVar pos var) =
    case env_lookup env var of
        Nothing -> Right (Err pos "undefined variable found")
        Just t -> Left t

infer_type env (EUnary pos op e) = case op of
    UNeg -> check_type1 env e Int Int (Err pos "argument of negation should be an integers")
    UNot -> check_type1 env e Bool Bool (Err pos "argument of not should be a boolean")

infer_type env (EBinary pos op e1 e2) =
    case operator_type op of
        Arithmetic -> check_type2 env e1 Int e2 Int Int (Err pos "both arguments of an arithemtic operator should be integers")
        Boolean -> check_type2 env e1 Bool e2 Bool Bool (Err pos "both arguments of a boolean operator should be boolean")
        Comparative -> check_type2 env e1 Int e2 Int Bool (Err pos "both arguments of a comparison should be integers")

infer_type env (ELet _ var e1 e2) =
    case infer_type env e1 of
        Left t -> let env1 = extend_env env var t in infer_type env1 e2
        Right err -> Right err

infer_type env (EIf pos e1 e2 e3) =
    case infer_type env e1 of
        Left Bool -> case infer_type env e2 of
            Left t -> check_type1 env e3 t t (Err pos "second and third expressions of an if statement should be of the same type")
            Right err -> Right err
        Right err -> Right err
        otherwise -> Right (Err pos "first expression of an if statement should be a boolean")

-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że wyrażenie e jest dobrze typowane, tzn.
-- typecheck (map fst input) e = Ok

construct_value :: (Var, Integer) -> (Var, Value)
construct_value (a, b) = (a, Left b)

count_op1 :: Env Value -> (Value -> a) -> (a -> a) -> (a -> Value) -> Expr p -> Maybe Value
count_op1 env from f to e1 =
    case count env e1 of
        Just val -> (Just . to . f . from) val
        otherwise -> Nothing

count_op2 :: Env Value -> (Value -> a) -> (a -> a -> Maybe b) -> (b -> Value) -> Expr p -> Expr p -> Maybe Value
count_op2 env from f to e1 e2 =
    case (count env e1, count env e2) of
        (Just val1, Just val2) -> case f (from val1) (from val2) of
            Nothing -> Nothing
            Just val -> (Just . to) val
        otherwise -> Nothing

count :: Env Value -> Expr p -> Maybe Value

count env (ENum _ n) = Just (Left n)
count env (EBool _ b) = Just (Right b)
count env (EVar _ var) = env_lookup env var

count env (EUnary _ op e) =
    case op of
        UNot -> count_op1 env fromRight not Right e
        UNeg -> count_op1 env fromLeft (*(-1)) Left e

count env (EBinary _ op e1 e2) =
    case op of
        BAnd -> count_op2 env fromRight (always (&&)) Right e1 e2
        BOr -> count_op2 env fromRight (always (||)) Right e1 e2
        BEq -> count_op2 env fromLeft  (always (==)) Right e1 e2
        BNeq -> count_op2 env fromLeft (always (/=)) Right e1 e2
        BLt -> count_op2 env fromLeft (always (<)) Right e1 e2
        BGt -> count_op2 env fromLeft (always (>)) Right e1 e2
        BLe -> count_op2 env fromLeft (always (<=)) Right e1 e2
        BGe -> count_op2 env fromLeft (always (>=)) Right e1 e2
        BAdd -> count_op2 env fromLeft (always (+)) Left e1 e2
        BSub -> count_op2 env fromLeft (always (-)) Left e1 e2
        BMul -> count_op2 env fromLeft (always (*)) Left e1 e2
        BDiv -> count_op2 env fromLeft (chk_snd div) Left e1 e2
        BMod -> count_op2 env fromLeft (chk_snd mod) Left e1 e2
    where
        always f a b = Just (f a b)
        chk_snd f a b = if b == 0 then Nothing else Just (f a b)

count env (ELet _ var e1 e2) =
    case count env e1 of
        Nothing -> Nothing
        Just val -> let env1 = extend_env env var val in count env1 e2

count env (EIf _ e1 e2 e3) =
    case count env e1 of
        Nothing -> Nothing
        Just (Right True) -> count env e2
        Just (Right False) -> count env e3

eval :: [(Var,Integer)] -> Expr p -> EvalResult
eval vars e =
    case count env e of
        Nothing -> RuntimeError
        Just (Left n) -> Value n
    where
        var_values = Prelude.map construct_value vars
        env = init_env var_values
