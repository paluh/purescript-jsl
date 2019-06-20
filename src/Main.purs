module Main where

import Prelude

import Control.Monad.Writer (Writer, execWriter, tell)
import Data.Array (singleton) as Array
import Data.Exists (Exists, mkExists, runExists)
import Data.Leibniz (type (~), coerce)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Class.Console (log)
import Effect.Random (random) as Random
import Language.JS.AST (BinaryOperator(..)) as AST
import Language.JS.AST (JS(..))
import Language.JS.Pretty (print, print1)
import Unsafe.Coerce (unsafeCoerce)

foreign import data Null ∷ Type
foreign import null_ ∷ Null

data Lit a
  = LNum Number (Number ~ a)
  | LString String (String ~ a)
  | LNull (Null ~ a)
  -- | LArray (∀ e t. Array e t ⇒ { arr ∷ Array (Expr var e), proof ∷ a ~ t })

num ∷ ∀ var. Number → Expr var Number
num n = ELit $ LNum n identity

data Lam var o' i o = Lam (Expr var i → Expr var o) (i → Expr var i) ((i → o) ~ o')
data App var o i = App (Expr var (i → o)) (Expr var i)


-- data ArrayExpr a e = ArrayExpr (Array (Expr var e)) (Array e ~ a)

-- | We want to be able to interpret (Lam (Expr var i → Expr var o)) as (i → o).
-- | This class allows us to do so.
class ToExpr e where
  expr ∷ ∀ var. e → Expr var e

instance toExprNumber ∷ ToExpr Number where
  expr n = ELit (LNum n identity)

instance toExprString ∷ ToExpr String where
  expr s = ELit (LString s identity)

instance toExprNull ∷ ToExpr Null where
  expr _ = ELit (LNull identity)

foreign import data Exists2 ∷ (Type → Type → Type) → Type

mkExists2 ∷ ∀ f a b. f a b → Exists2 f
mkExists2 = unsafeCoerce

runExists2 ∷ ∀ f r. (∀ a b. f a b → r) → Exists2 f → r
runExists2 = unsafeCoerce

data Expr var a
  = ELit (Lit a)
  | EAdd (Expr var Number) (Expr var Number) (Number ~ a)
  | ESub (Expr var Number) (Expr var Number) (Number ~ a)
  | EMul (Expr var Number) (Expr var Number) (Number ~ a)
  | EDiv (Expr var Number) (Expr var Number) (Number ~ a)
  | EAppendStr (Expr var String) (Expr var String) (String ~ a)
  | ELam (Exists2 (Lam var a))
  | EApp (Exists (App var a))
  | EVar var
-- | Just for testing
  | EToString (Expr var Number) (String ~ a)
-- | EArr (Exists (ArrayExpr a))
--
instance monoidExprString ∷ Monoid (Expr var String) where
  mempty = ELit (LString "" identity)

instance semigroupExprString ∷ Semigroup (Expr var String) where
  append s1 s2 = EAppendStr s1 s2 identity

instance semiringExprNum ∷ Semiring (Expr var Number) where
  zero = ELit (LNum 0.0 identity)
  add e1 e2 = EAdd e1 e2 identity
  one = ELit (LNum 1.0 identity)
  mul e1 e2 = EMul e1 e2 identity

instance ringExprNum ∷ Ring (Expr var Number) where
  sub e1 e2 = ESub e1 e2 identity

instance commutativeRingExprNum ∷ CommutativeRing (Expr var Number)

instance euclideanRingExprNum ∷ EuclideanRing (Expr var Number) where
  degree _ = 1
  div e1 e2 = EDiv e1 e2 identity
  mod _ _ = zero

-- -- arr ∷ ∀ e. Array (Expr var e) → Expr var (Array e)
-- -- arr exprs = EArr $ mkExists (ArrayExpr exprs identity)
interpretBinary' ∷ ∀ a. (a → a → a) → Expr Void a → Expr Void a → a
interpretBinary' op e1 e2 = op (interpret' e1) (interpret' e2)

interpret' ∷ ∀ a. Expr Void a → a
interpret' (ELit (LNum n proof)) = coerce proof n
interpret' (ELit (LString s proof)) = coerce proof s
interpret' (ELit (LNull proof)) = coerce proof null_
interpret' (EAdd e1 e2 proof) = coerce proof $ interpretBinary' (+) e1 e2
interpret' (ESub e1 e2 proof) = coerce proof $ interpretBinary' (-) e1 e2
interpret' (EMul e1 e2 proof) = coerce proof $ interpretBinary' (*) e1 e2
interpret' (EDiv e1 e2 proof) = coerce proof $ interpretBinary' (/) e1 e2
interpret' (EToString e proof) = coerce proof $ (show $ interpret' e)
interpret' (EAppendStr s1 s2 proof) = coerce proof $ interpretBinary' append s1 s2
interpret' (EApp app) =
  (runExists (\x → let App l arg = x in (interpret' l) (interpret' arg)) app)
interpret' (ELam l) =
  (runExists2 (\(Lam f exp proof) → (coerce proof \x → interpret' (f (exp x)))) l)
interpret' (EVar _) = unsafeCoerce "Void value?"

interpretBinary ∷ ∀ a. AST.BinaryOperator → Expr String a → Expr String a → Maybe JS
interpretBinary op i1 i2 = do
  i1' ← interpret i1
  i2' ← interpret i2
  pure (JSBinary op i1' i2')

interpret ∷ ∀ a. Expr String a → Maybe JS
interpret (ELit (LNull _)) = Just $ JSNullLiteral
interpret (ELit (LNum n _)) = Just $ JSNumericLiteral n
interpret (ELit (LString s _)) = Just $ JSStringLiteral s
interpret (EAdd n1 n2 _) = interpretBinary AST.Add n1 n2
interpret (EMul n1 n2 _) = interpretBinary AST.Multiply n1 n2
interpret (ESub n1 n2 _) = interpretBinary AST.Subtract n1 n2
interpret (EDiv n1 n2 _) = interpretBinary AST.Divide n1 n2
interpret (EAppendStr s1 s2 _) = interpretBinary AST.Add s1 s2
interpret (EVar n) = pure (JSVar n)
interpret (EApp app) =
  (runExists (\x → let App l arg = x in (\f a → JSApp f [a])  <$> (interpret l) <*> interpret arg) app)
interpret (ELam app) =
  runExists2 (\(Lam f _ _) → JSFunction Nothing ["x"] <<< JSBlock <<< Array.singleton <<< JSReturn <$> (interpret $ f (EVar "x"))) app
interpret (EToString n _) = do
  n' ← interpret n
  pure (JSApp (JSAccessor "toString" n') [])

newtype JS' a = JS' JS

interpretJS ∷ ∀ a. Expr String a → Maybe (JS' a)
interpretJS = map JS' <<< interpret

lambda ∷ ∀ i o var. ToExpr i ⇒ (Expr var i →  Expr var o) → Expr var (i → o)
lambda f = ELam (mkExists2 (Lam f expr identity))

toString ∷ ∀ var. Expr var Number → Expr var String
toString n = EToString n identity

app ∷ ∀ i o var. (Expr var (i → o)) → Expr var i → Expr var o
app l arg = EApp (mkExists (App l arg))

nineExpr = app (lambda \n → toString (n + (expr 8.0))) (expr 1.0)

data Free f a
  = Free (f (Free f a))
  | Pure a

instance functorFree ∷ Functor f ⇒ Functor (Free f) where
  map g (Pure a) = Pure (g a)
  map g (Free f) = Free (map (map g) f)

instance applyFree ∷ Functor f ⇒ Apply (Free f) where
  apply (Pure g) fa = map g fa
  apply (Free fg) fa = Free (map (flip apply fa) fg)

instance applicativeFree ∷ Functor f ⇒ Applicative (Free f) where
  pure = Pure

instance bindFree ∷ Functor f ⇒ Bind (Free f) where
  bind (Pure a) g = g a
  bind (Free fa) g = Free (map (flip bind g) fa)

instance monadFree ∷ Functor f ⇒ Monad (Free f)

liftF ∷ ∀ a f. Functor f ⇒ f a → Free f a
liftF f = Free (map Pure f)

data SVar' var a i = SVar' (Expr var i) (Expr var i → a)

data StatementF var a
  = SRandom (Expr var Number → a)
  | SConsoleLog (Expr var String) a
  | SVar (Exists (SVar' var a))
  -- | SFun (Exists2 (SFun' var a))

-- | Writing functor by hand because we want to be able
-- | to map over polymorphic `SVar`.
instance functorStatementF ∷ Functor (StatementF var) where
  map f (SRandom g) = SRandom (map f g)
  map f (SConsoleLog e a) = SConsoleLog e (f a)
  map f (SVar ex) = runExists (\(SVar' e i) → SVar (mkExists (SVar' e (map f i)))) ex
  -- map f (SFun ex) = runExists2 (\(SFun' sf proof) → mkExists2 (SFun' (map (map f) sf) (unsafeCoerce proof))) ex


type Statement var = Free (StatementF var)

type Statement' var a = Statement var (Expr var a)

newtype Function var i o = Function (Expr var i → Statement' var o)

fun' ∷ ∀ i o. ToExpr i ⇒ Function Void i o → i → Effect o
fun' (Function f) = \i → run' (f (expr i))

run' ∷ ∀ a. Statement Void (Expr Void a) → Effect a
run' (Free (SRandom f)) = do
  n ← Random.random
  run' (f (expr n))
run' (Free (SVar ex)) = do
  run' $ runExists (\(SVar' a c) → c a) ex
run' (Free (SConsoleLog es a)) = do
  let
    s = interpret' es
  log s
  run' a
run' (Pure expr) = pure $ interpret' expr

-- | XXX: add var sequence
-- | Add phantom type which indicates result type of an expression
type JsM a = Writer (Array JS) a

fun ∷ ∀ i o. Function String i o → JsM Unit
fun (Function f) =
  let
    i = EVar "input"
  in do
    let
      statements = execWriter (run (f i))
    tell [ JSFunction Nothing ["input"] $ JSBlock statements ]

run ∷ ∀ a. Statement String (Expr String a) → JsM Unit
run (Free (SRandom f)) = do
  tell [ JSVariableIntroduction "r" (Just (JSApp (JSAccessor "random" (JSVar "Math")) [])) ]
  run (f (EVar "r"))
run (Free (SVar ex)) = runExists (\(SVar' x c) → do
  let
    value = case interpret x of
      Nothing → Nothing
      Just v → Just v
  tell [ JSVariableIntroduction "z" value ]
  run (c (EVar "z")))
  ex
run (Free (SConsoleLog es a)) = do
  -- | XXX: This should not be maybe
  let
    args = case interpret es of
      Nothing → []
      Just v → [v]
  tell [ (JSApp (JSAccessor "log" (JSVar "console")) args) ]
  run a
run (Pure es) = do
  case (interpret es) of
    Just v → tell [ v ]
    Nothing → pure unit

random ∷ ∀ var. Statement' var Number
random = liftF (SRandom identity)

consoleLog ∷ ∀ var. Expr var String → Statement' var Null
consoleLog s = liftF (SConsoleLog s (expr null_))

var ∷ ∀ a var. Expr var a → Statement' var a
var e = liftF (SVar (mkExists (SVar' e identity)))

lottery = Function \input → do
  n ← random
  addRandom ← var (lambda \z → z + n + input)
  -- m ← random
  -- x ← var (expr "Test")
  void $ consoleLog (expr "Random number was:")
  void $ consoleLog (toString n)
  void $ consoleLog (expr "And random +10.0 is:")
  consoleLog (toString (app addRandom $ expr 10.0))

main ∷ Effect Unit
main = do
  log (show (interpret' nineExpr))
  case print1 <$> interpret nineExpr of
    Nothing → pure unit
    Just js → log js

  let
    js = print $ execWriter (fun lottery)
  void $ (fun' lottery 9.0)
  log js
  pure unit
