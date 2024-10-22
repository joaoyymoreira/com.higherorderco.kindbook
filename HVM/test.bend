Main =
  use n = λfλx(f (f (f (f (f (f (f (f (f (f (f (f x))))))))))))
  use m = λsλz(n (n s) z)
  use f = λb(b λtλf(f) λtλf(t))
  use x = λtλf(t)
  (m f x)
