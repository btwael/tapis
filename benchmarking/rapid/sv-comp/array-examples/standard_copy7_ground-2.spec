func main()
{
  const Int blength;
  const Int[] a1;
  Int[] a2;
  Int[] a3;
  Int[] a4;
  Int[] a5;
  Int[] a6;
  Int[] a7;
  Int[] a8;

  Int i = 0;
  while(i < blength)
  {
    a2[i] = a1[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a3[i] = a2[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a4[i] = a3[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a5[i] = a4[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a6[i] = a5[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a7[i] = a6[i];
    i = i + 1;
  }

  i = 0;
  while(i < blength)
  {
    a8[i] = a7[i];
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
      (= (a1 x) (a8 main_end x))
    )
  )
)
