--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Type Inference Project         --
--                                        --
--------------------------------------------


------------------------- Auxiliary functions
find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

qsort :: Ord a => [a] -> [a]
qsort []     = []
qsort (p:xs) = (qsort lesser) ++ [p] ++ (qsort greater)
    where
        lesser  = filter (< p) xs
        greater = filter (>= p) xs

uniq :: Eq a => [a] -> [a]
uniq [] = []
uniq (x:xs) = x : uniq (filter (/=x) xs)
------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"

t4 :: Type
t4 = (At "c" :-> At "b") :-> (At "c" :-> At "d")


------------------------- Assignment 1
-- BAD IMPLEMENTATION OF FUNCTIONAL PROGRAMMING BUT WILL BE BETTER LATER ON --
occurs :: Atom -> Type -> Bool
occurs z (At x)
 | z==x = True
 | otherwise = False
occurs z (At x :-> s)
 | z==x = True
 | otherwise = occurs z s
occurs z (s :-> At x)
 | z==x = True
 | otherwise = occurs z s
occurs z (t :-> v)
 | occurs z t == True = True
 | otherwise = occurs z v

findAtoms :: Type -> [Atom]
findAtoms (At x) = [x]
findAtoms (t :-> v) = uniq(qsort(findAtoms t ++ findAtoms v))

------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub s (At x)
 | x==fst(s) = snd(s)
 | otherwise = At x
sub s (t :-> v) = sub s t :-> sub s v

subs :: [Sub] -> Type -> Type
subs (x:xs) (At a)
 | null xs && a==fst(x) = snd(x)
 | null xs && a/=fst(x) = At a
 | otherwise = sub x (subs xs (At a))
subs s (t :-> v) = subs s t :-> subs s v

------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3

--Used to convert unification pair to substitution pair
convertToSub :: Upair -> Sub
convertToSub (At a, s) = (a, s)
convertToSub (s, At a) = (a, s)

--Used in case c (σ1 → σ2) ↔ (τ1 → τ2): (S, {σ1 ↔ τ1, σ2 ↔ τ2} ∪ U)
convertToUpairs :: Upair -> [Upair]
convertToUpairs (s:->t,x:->v) = [(s,x) , (t,v)]

--checks unification pair to determine which transitions to perform
checkRule :: Upair -> Int
checkRule (At a, t:->v) = 2
checkRule (t:->v, At a) = 2
checkRule (t:->v, s:->z) = 3
checkRule (At a, At b)
 | a==b = 1
 | otherwise = 4

--used in case b to determine if an atom occurs in the corresponding type
checkOccurs :: Upair->Bool
checkOccurs (At a , s)
 | occurs a s = False
 | otherwise = True
checkOccurs (s, At a)
 | occurs a s = False
 | otherwise = True

sub_u :: Sub -> [Upair] -> [Upair]
sub_u s [] = []
sub_u s (x:xs) = (sub s (fst(x)), sub s (snd(x))) : sub_u s (xs) 

step :: State -> State
step (s,(x:xs))
-- case a = α ↔ α : return (S, U);
 |checkRule x == 4 = ([convertToSub x]++s, sub_u (convertToSub x) xs)
 |checkRule x == 1 = (s,xs)
--case b = α ↔ τ or τ ↔ α : if α occurs in τ , FAIL;
--                        otherwise, return (S[τ/α], U[τ/α])
 |checkRule x == 2 && checkOccurs x = ([convertToSub x]++s, sub_u (convertToSub x) xs)
 |checkRule x == 2 && (checkOccurs x == False) = error "Step: atom occured in the corresponding type"
--case c = (σ1 → σ2) ↔ (τ1 → τ2): return (S, {σ1 ↔ τ1, σ2 ↔ τ2} ∪ U)
 |checkRule x == 3 = (s, (convertToUpairs x) ++ xs)
 

unify :: [Upair] -> [Sub]
unify [] = []
unify u = aux ([] , u)
 where
  aux :: State -> [Sub]
  aux ([],u) = aux(step ([],u))
  aux (s,u) 
   | null u = s
   | otherwise = aux(step (s,u)) 

------------------------- Assignment 4

type Context   = [(Var,Type)]
type Judgement = (Context,Term,Type)

data Derivation = Axiom Judgement | Abstraction Judgement Derivation| Application Judgement Derivation Derivation
 

n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Application a x y) = a
conclusion (Abstraction a x) = a
conclusion (Axiom a) = a


subs_ctx :: [Sub] -> Context -> Context
subs_ctx s [] = []
subs_ctx s (x:xs) = ( fst(x), subs s (snd x) ) : subs_ctx s xs

subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg s (c,t,v) = (subs_ctx s c, t , subs s v)

subs_der :: [Sub] -> Derivation -> Derivation
subs_der s (Application a x y) = Application (subs_jdg s a) (subs_der s x) (subs_der s y)
subs_der s (Abstraction a x) = Abstraction (subs_jdg s a) (subs_der s x)
subs_der s (Axiom a) = Axiom(subs_jdg s a)


------------------------- Typesetting derivations

instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])


------------------------- Assignment 5

--used to only REMOVE old occurrence of variables
--new occurence not added in this function
filterContext :: (Var, Type)-> [(Var, Type)] -> [(Var,Type)]
filterContext (v,t) [] = []
filterContext (v,t) [(s,z)]
 | v == s = []
 | v /= s = [(s,z)]
filterContext (v,t) (x:xs) = (filterContext (v,t) [x]) ++ (filterContext (v,t) xs)  

--used in derive0 and derive1
--converts terms with types into context
termToContext :: [Atom]->Term -> [(Var, Type)]
--derive0 use cases
termToContext [] (Variable v) = [(v,(At ""))]
termToContext [] (Lambda z (t)) = []
termToContext []  (Apply term1 term2) = (termToContext [] term1) ++ (termToContext [] term2)
--derive1 use cases
termToContext a  (Variable v) = [(v,(At (head a)))]
termToContext a  (Lambda z (t)) = []
termToContext a  (Apply term1 term2) = (termToContext (second a) term1) ++ (termToContext (first a) term2)


derive0 :: Term -> Derivation
derive0 t = aux(termToContext [] (t), t , At "")
  where
    aux :: Judgement -> Derivation
    aux (c,(Variable v),typ) = ( Axiom(c,(Variable v ),typ) )
    aux (c,(Lambda v  term1),typ) = ( Abstraction (c,(Lambda v  term1),typ) (aux(( ([(v,At "")] ++ (filterContext (v,At "") c)) , term1 ,  At ""))) )
    aux (c,(Apply term1 term2),typ) = ( Application (c,(Apply term1 term2),typ) (aux(c , term1, At "")) (aux ((c, term2, At ""))) )


first [] = []
first (x:xs) = x:second xs

second [] = []
second (x:xs) = first xs

--drops the first n elements and returns the rest of the list
dropList :: Int -> [Atom] -> [Atom]
dropList _ [] = []
dropList 0 ys = ys
dropList x ys = dropList (x-1) (tail ys)

derive1 :: Term -> Derivation
derive1 t = aux (dropList ( length (termToContext(tail atoms) t ) ) (tail atoms)) (termToContext (tail atoms) (t),t, At (head atoms))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux a (c,(Variable v),typ) = ( Axiom(c,(Variable v ),typ) )
    aux a (c,(Lambda v  term1),typ) = ( Abstraction (c,(Lambda v  term1),typ) (aux (tail (tail a)) (( ( [(v,At (a!!0))] ++ (filterContext (v,At (a!!0)) c))  , term1 ,  At (a!!1)))) )
    aux a (c,(Apply term1 term2),typ) = ( Application (c,(Apply term1 term2),typ) (aux (second (dropList 2 a)) (c , term1, At (a!!0))) (aux (first (dropList 2 a))  ((c, term2, At (a!!1)))) )

--returns type of derivation
getTerm :: Derivation -> Type
getTerm (Application (s,v,typ) x y) = typ
getTerm (Abstraction (s,v,typ) x) = typ
getTerm (Axiom (s,v,typ)) = typ

-- getDer used to get type of (x : α) within :     Γ, x : α |- M : β
--                                                -------------------
--                                                   Γ |- λx.M : γ
getDer :: Derivation -> Type
getDer (Application ((x:xs),v,typ) z y) = snd(x)
getDer (Abstraction ((x:xs),v,typ) z) = snd(x)
getDer (Axiom ((x:xs),(Variable v),typ))
 | fst(x) == v = snd(x)
 | otherwise = getDer (Axiom(xs,(Variable v),typ))

upairs :: Derivation -> [Upair]
upairs (Axiom ((x:xs),v,typ)) = [(typ,getDer( Axiom ((x:xs),v,typ) )) ]
upairs (Abstraction (s,v,typ) x) = [(typ,getDer(x) :-> getTerm(x))] ++ upairs(x)
upairs (Application (s,v,typ) x y) = [(getTerm(x) , getTerm(y) :-> typ )] ++ upairs(x) ++ upairs(y)

derive :: Term -> Derivation
derive t = subs_der (unify(upairs (derive1 t))) (derive1 t)