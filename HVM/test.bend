#(Foo 0) = 0
#(Foo n) =
  #let f0 = λb(b λtλf(f) λtλf(t))
  #let f1 = λx(f0 (f0 x))
  #let f2 = λx(f1 (f1 x))
  #let f3 = λx(f2 (f2 x))
  #let f4 = λx(f3 (f3 x))
  #let f5 = λx(f4 (f4 x))
  #let f6 = λx(f5 (f5 x))
  #let f7 = λx(f6 (f6 x))
  #let f8 = λx(f7 (f7 x))
  #let f9 = λx(f8 (f8 x))
  #let fA = λx(f9 (f9 x))
  #let fB = λx(fA (fA x))
  #let fC = λx(fB (fB x))
  #let fD = λx(fC (fC x))
  #let fE = λx(fD (fD x))
  ##let fF = λx(fE (fE x))
  ##let fG = λx(fF (fF x))
  #((fE λtλf(t)) (Foo (- n 1)) 0)

#Main =
  #(Foo 1)


#Main = (λaλb(a b) λx(x) λy(y))
Main = (λx(x) λx(x))



  #use n = λfλx(f (f (f (f (f (f (f (f (f (f (f (f x))))))))))))
  #use m = λsλz(n (n s) z)
  #use k = λsλz(m (m s) z)
  #use f = λb(b λtλf(f) λtλf(t))
  #use x = λtλf(t)
  #(k f x)
