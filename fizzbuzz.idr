
-- A constructive proof that a number is fizzy (divisible by 3)
data Fizzy : (n : Nat) -> Type where
  ZeroFizz : Fizzy Z
  Fizz : Fizzy n -> Fizzy (3 + n)

-- forall x, forall y. 1 + (x + y) = x + (1 + y)
total
plusSuccRightSucc : (x, y : Nat) -> S (x + y) = x + (S y)
plusSuccRightSucc Z y = Refl
plusSuccRightSucc (S k) y = rewrite rec in Refl
  where
    rec : S (plus k y) = plus k (S y)
    rec = plusSuccRightSucc k y

total
iterate : (f : a -> a) -> a -> Stream a
iterate f x = x :: iterate f (f x)

-- forall 'Fizzy n' there exists a natural number 'k' such that n = 3k.
total
fizzyCorrect : (n : Nat) -> Fizzy n -> (k : Nat ** n = 3 * k)
fizzyCorrect Z ZeroFizz = (Z ** Refl)
fizzyCorrect (S (S (S x))) (Fizz y) = 
  let (w ** rec) = fizzyCorrect x y
      p1 = plusSuccRightSucc w (plus w 0)
      p2 = plusSuccRightSucc w (S (plus w (plus w 0)))
      p3 = plusSuccRightSucc w (plus w (plus w 0))
  in (S w ** rewrite rec in 
             rewrite sym p1 in 
             rewrite sym p2 in 
             rewrite sym p3 in 
             Refl)

-- A proof that 'Fizzy 1' implies a contradiction
total
oneNotFizzy : Not (Fizzy 1)
oneNotFizzy (Fizz f) impossible

-- A proof that 'Fizzy 2' implies a contradiction
total
twoNotFizzy : Not (Fizzy 2)
twoNotFizzy (Fizz f) impossible

-- forall n. If 'Fizzy n' implies a contradiction then so does 'Fizzy (3 + n)'
total
fizzyUp : Not (Fizzy n) -> Not (Fizzy (3 + n))
fizzyUp cant ZeroFizz impossible
fizzyUp cant (Fizz f) = cant f

-- forall n. 'Fizzy n' is decidable
total
decFizzy : (n : Nat) -> Dec (Fizzy n)
decFizzy Z = Yes ZeroFizz
decFizzy (S Z) = No oneNotFizzy
decFizzy (S (S Z)) = No twoNotFizzy
decFizzy (S (S (S k))) with (decFizzy k)
  decFizzy (S (S (S k))) | Yes prf = Yes (Fizz prf)
  decFizzy (S (S (S k))) | No contra = No (fizzyUp contra)

-- A constructive proof that a number is Buzzy (divisible by 5)
data Buzzy : (n : Nat) -> Type where
  ZeroBuzz : Buzzy Z
  Buzz : Buzzy n -> Buzzy (5 + n)
    
-- forall 'Buzzy n' there exists a natural number 'k' such that n = 5k.
total
buzzyCorrect : (n : Nat) -> Buzzy n -> (k : Nat ** n = 5 * k)
buzzyCorrect Z ZeroBuzz = (Z ** Refl)
buzzyCorrect (S (S (S (S (S x))))) (Buzz y) = 
  let (w ** rec) = buzzyCorrect x y
      p1 = plusSuccRightSucc w (plus w 0)
      p2 = plusSuccRightSucc w (S (plus w (plus w 0)))
      p3 = plusSuccRightSucc w (plus w (plus w 0))
      p4 = plusSuccRightSucc w (S (S (plus w (plus w (plus w 0)))))
      p5 = plusSuccRightSucc w (S (plus w (plus w (plus w 0))))
      p6 = plusSuccRightSucc w (plus w (plus w (plus w 0)))
      p7 = plusSuccRightSucc w 
           (S (S (S (plus w (plus w (plus w (plus w 0)))))))
      p8 = plusSuccRightSucc w
           (S (S (plus w (plus w (plus w (plus w 0))))))
      p9 = plusSuccRightSucc w (S (plus w (plus w (plus w (plus w 0)))))
      p10 = plusSuccRightSucc w (plus w (plus w (plus w (plus w 0))))
  in (S w ** rewrite rec in
             rewrite sym p1 in
             rewrite sym p2 in
             rewrite sym p3 in
             rewrite sym p4 in
             rewrite sym p5 in
             rewrite sym p6 in
             rewrite sym p7 in
             rewrite sym p8 in
             rewrite sym p9 in
             rewrite sym p10 in
             Refl)

-- A proof that 'Buzzy 1' implies a contradiction
total
oneNotBuzzy : Not (Buzzy 1)
oneNotBuzzy (Buzz 1) impossible

-- A proof that 'Buzzy 2' implies a contradiction
total
twoNotBuzzy : Not (Buzzy 2)
twoNotBuzzy (Buzz 2) impossible

-- A proof that 'Buzzy 3' implies a contradiction
total
threeNotBuzzy : Not (Buzzy 3)
threeNotBuzzy (Buzz 3) impossible

-- A proof that 'Buzzy 4' implies a contradiction
total
fourNotBuzzy : Not (Buzzy 4)
fourNotBuzzy (Buzz 4) impossible

-- If 'Buzzy x' implies a contridiction then so does
-- 'Buzzy (x + 5)'
total
buzzyUp : Not (Buzzy x) -> Not (Buzzy (5 + x))
buzzyUp cant ZeroBuzz impossible
buzzyUp cant (Buzz f) = cant f

-- Buzziness is decidable.
decBuzzy : (n : Nat) -> Dec (Buzzy n)
decBuzzy Z = Yes ZeroBuzz
decBuzzy (S Z) = No oneNotBuzzy
decBuzzy (S (S Z)) = No twoNotBuzzy
decBuzzy (S (S (S Z))) = No threeNotBuzzy
decBuzzy (S (S (S (S Z)))) = No fourNotBuzzy
decBuzzy (S (S (S (S (S k))))) with (decBuzzy k)
  decBuzzy (S (S (S (S (S k))))) | Yes prf = 
    Yes (Buzz prf)
  decBuzzy (S (S (S (S (S k))))) | No cant =
    No (buzzyUp cant)

-- If fizziness is decidable and buzziness is also
-- decidable then both are decidable.
fizzBuzz : (n : Nat) -> String
fizzBuzz n with (decFizzy n, decBuzzy n)
  fizzBuzz n | (Yes prf, No cant) = "Fizz"
  fizzBuzz n | (No cant, Yes prf) = "Buzz"
  fizzBuzz n | (Yes prf, Yes prf2) = "FizzBuzz"
  fizzBuzz n | (No cant, No contra) = show n

nats : Stream Nat
nats = iterate S Z

go : String
go = show (take 20 (map fizzBuzz nats))

