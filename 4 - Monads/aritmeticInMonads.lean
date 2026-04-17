/- ============================= -/
/- Example: Arithmetic in Monads -/
/- ============================= -/

-- Monads are a way of encoding programs with side effects into a language that does not have them.

/- ---------------------- -/
/- Arithmetic Expressions -/
/- ---------------------- -/

inductive Expr (op : Type) where
  | const : Int → Expr op                     -- constant
  | prim  : op → Expr op → Expr op → Expr op  -- primitive binary operator
deriving Repr

inductive Arith where
  | plus
  | minus
  | times
  | div
deriving Repr

-- expression 2 + 3
open Expr Arith
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

#eval twoPlusThree                        

-- expression 14 / (45 - 5 * 9) == 14 / 0
open Expr Arith
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5) (const 9)))

#eval fourteenDivided                     

/- ---------------------- -/
/- Evaluating Expressions -/
/- ---------------------- -/

-- division can fail -> result is an Option
def evaluateOption1 : Expr Arith → Option Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateOption1 e1 >>= fun v1 =>
                         evaluateOption1 e2 >>= fun v2 =>
                         match p with
                         | plus  => pure (v1 + v2)
                         | minus => pure (v1 - v2)
                         | times => pure (v1 * v2)
                         | div   => if v2 == 0
                                      then none
                                      else pure (v1 / v2)

 def applyPrimOption : Arith → Int → Int → Option Int
  | plus,  x, y => pure (x + y)
  | minus, x, y => pure (x - y)
  | times, x, y => pure (x * y)
  | div,   x, y => if y == 0
                     then none
                     else pure (x / y)

def evaluateOption2 : Expr Arith → Option Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateOption1 e1 >>= fun v1 =>
                         evaluateOption1 e2 >>= fun v2 =>
                         applyPrimOption p v1 v2                        
                         
#eval evaluateOption1 fourteenDivided       
#eval evaluateOption1 twoPlusThree          

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus,  x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div,   x, y => if y == 0
                           then Except.error s!"Tried to divide {x} by zero"
                           else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateExcept e1 >>= fun v1 =>
                         evaluateExcept e2 >>= fun v2 =>
                         applyPrimExcept  p v1 v2

#eval evaluateExcept fourteenDivided         
#eval evaluateExcept twoPlusThree            

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateM applyPrim e1 >>= fun v1 =>
                         evaluateM applyPrim e2 >>= fun v2 =>
                         applyPrim p v1 v2

#eval evaluateM applyPrimOption fourteenDivided
#eval evaluateM applyPrimOption twoPlusThree   
#eval evaluateM applyPrimExcept fourteenDivided
#eval evaluateM applyPrimExcept twoPlusThree   

def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0
      then none
      else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0
      then Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)

def applyPrim' [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | plus,  x, y => pure (x + y)
  | minus, x, y => pure (x - y)
  | times, x, y => pure (x * y)
  | div,   x, y => applyDiv x y

def evaluateM' [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateM' applyDiv e1 >>= fun v1 =>
                         evaluateM' applyDiv e2 >>= fun v2 =>
                         applyPrim' applyDiv p v1 v2

#eval evaluateM' applyDivOption fourteenDivided
#eval evaluateM' applyDivOption twoPlusThree   
#eval evaluateM' applyDivExcept fourteenDivided
#eval evaluateM' applyDivExcept twoPlusThree   

/- --------------- -/
/- Further Effects -/
/- --------------- -/

inductive CanFail where
  | div

inductive Prim where
  | plus
  | minus
  | times
  | other : CanFail → Prim

def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0
                           then none 
                           else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y => if y == 0
                           then Except.error s!"Tried to divide {x} by zero"
                           else pure (x / y)

def applyPrim'' [Monad m] (applyCanFail : CanFail → Int → Int → m Int) : Prim → Int → Int → m Int
  | Prim.plus,     x, y => pure (x + y)
  | Prim.minus,    x, y => pure (x - y)
  | Prim.times,    x, y => pure (x * y)
  | Prim.other op, x, y => applyCanFail op x y

def evaluateM'' [Monad m] (applyCanFail : CanFail → Int → Int → m Int) : Expr Prim → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateM'' applyCanFail e1 >>= fun v1 =>
                         evaluateM'' applyCanFail e2 >>= fun v2 =>
                         applyPrim'' applyCanFail p v1 v2

-- expression 2 + 3
open Expr Prim CanFail
def twoPlusThree' : Expr Prim :=
  prim plus (const 2) (const 3)

-- expression 14 / (45 - 5 * 9) == 14 / 0
open Expr Prim CanFail
def fourteenDivided' : Expr Prim :=
  prim (other div) (const 14)
    (prim minus (const 45)
      (prim times (const 5) (const 9)))


#eval evaluateM'' divOption fourteenDivided'
#eval evaluateM'' divOption twoPlusThree'   
#eval evaluateM'' divExcept fourteenDivided'
#eval evaluateM'' divExcept twoPlusThree'   

/- ---------- -/
/- No Effects -/
/- ---------- -/

-- Empty is as an indication to the type system that a function cannot be called.

#check Empty

inductive Prim' (special: Type) where
  | plus
  | minus
  | times
  | other : special → Prim' special

inductive CanFail' where
  | div

-- Using Empty as the parameter to Prim indicates that there are no additional cases beyond Prim.plus, Prim.minus, and Prim.times,
-- because it is impossible to come up with a value of type Empty to place in the Prim'.other constructor.
def applyPrim''' [Monad m] (applySpecial : special → Int → Int → m Int) : Prim' special → Int → Int → m Int
  | Prim'.plus,     x, y => pure (x + y)
  | Prim'.minus,    x, y => pure (x - y)
  | Prim'.times,    x, y => pure (x * y)
  | Prim'.other op, x, y => applySpecial op x y

def evaluateM''' [Monad m] (applySpecial : special → Int → Int → m Int) : Expr (Prim' special) → m Int
  | Expr.const i      => pure i
  | Expr.prim p e1 e2 => evaluateM''' applySpecial e1 >>= fun v1 =>
                         evaluateM''' applySpecial e2 >>= fun v2 =>
                         applyPrim''' applySpecial p v1 v2

-- Using the syntax `nomatch E` when E is an expression whose type has no constructors
-- indicates to Lean that the current expression need not return a result, because it
-- could never have been called.
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op

-- together with the identity monad Id this can be used to evaluate expressions that have no effects whatsoever
#eval evaluateM''' (m := Id) applyEmpty $ prim Prim'.plus (const 5) (const (-14))

/- ----------------------- -/
/- Nondeterministic Search -/
/- ----------------------- -/

inductive Many (α : Type) where
  | none : Many α                          -- no   answer (like list's nil)
  | more : α → (Unit → Many α) → Many α    -- more answers; function ´Unit → Many α´ calculates next value; more is like list's cons function

-- store x in list like structure; no next value
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)

def Many.union : Many α → Many α → Many α
  | Many.none, ys     => ys
  | Many.more x f, ys => Many.more x (fun () => union (f ()) ys)

def Many.fromList : List α → Many α
  | []      => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _                 => []
  | _, Many.none         => []
  | n + 1, Many.more x f => x :: (f ()).take n

def Many.takeAll : Many α → List α
  | Many.none     => []
  | Many.more x f => x :: (f ()).takeAll

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _     => Many.none
  | Many.more x f, g => (g x).union $ bind (f ()) g

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

-- finds all the combinations of numbers in a list that add to goal
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | []      => if goal == 0
                 then pure []
                 else Many.none
  | x :: xs => if x > goal
                 then addsTo goal xs
                 else (addsTo goal xs).union
                        (addsTo (goal - x) xs >>= fun answer =>
                            pure $ x :: answer)

def printList [ToString α] : List α → IO Unit
  | []      => pure ()
  | x :: xs => do IO.println x
                  printList xs

#eval (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll          
#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll

inductive NeedsSearch
  | choose
  | div

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y => Many.fromList [x, y]
  | NeedsSearch.div,    x, y => if y == 0
                                  then Many.none
                                  else Many.one (x / y)

open Expr Prim' NeedsSearch
#eval (evaluateM''' applySearch                                
        (prim plus (const 1)
          (prim (other choose) (const 2) (const 5)))).takeAll

#eval (evaluateM''' applySearch                                
        (prim plus (const 1)
          (prim (other div) (const 2) (const 0)))).takeAll

#eval (evaluateM''' applySearch                                
        (prim (other div) (const 90)
          (prim plus
            (prim (other choose) (const (-5)) (const 5))
            (const 5)))).takeAll

/- ------------------- -/
/- Custom Environments -/
/- ------------------- -/

-- The mapping from function names to function implementations is called an ENVIRONMENT.

-- Using functions as a monad is typically called a READER MONAD. 

-- by convention ρ is used for environments
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x

-- Reader ρ α → (α → Reader ρ β) → Reader ρ β == (ρ → α) → (α → ρ → β) → (ρ → β)
-- def Reader.bind {ρ : Type} {α : Type} {β : Type} (result : ρ → α) (next : α → ρ → β) : ρ → β :=
--  fun env => next (result env) env

def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env

instance : Monad (Reader ρ) where
  pure x   := fun _ => x
  bind x f := fun env => f (x env) env
  
abbrev Env : Type := List (String × (Int → Int → Int))

def exampleEnv : Env := [("max", max),
                         ("mod", (· % ·))]

-- returns 0 if the function is unknown
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env => match env.lookup op with
                      | none   => pure 0
                      | some f => pure (f x y)

#eval evaluateM'' applyPrimReader                            
        (prim (other "max") (prim plus (const 5) (const 4))
          (prim times (const 3) (const 2)))
        exampleEnv

/- --------- -/
/- Exercises -/
/- --------- -/

/- ------------------ -/
/- Checking Contracts -/
/- ------------------ -/

/- -------------------- -/
/- Readers with Failure -/
/- -------------------- -/

/- ------------------- -/
/- A Tracing Evaluator -/
/- ------------------- -/
