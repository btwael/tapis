func main()
{
  const Int blength;
  Int[] a;
  Int[] b;

  Int i = 0;
  while(i < blength)
  {
    a[i] = 42;
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    b[i] = a[i];
    i = i + 1;
  }
}

(conjecture
  (forall ((x Int))
    (=>
      (and
        (> blength 0)
        (<= 0 x)
        (< x blength)
      )
      (= (b main_end x) 42)
    )
  )
)
