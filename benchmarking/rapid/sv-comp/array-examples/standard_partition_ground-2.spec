func main()
{
  const Int blength;
  Int[] aa;
  Int[] bb;
  Int[] cc;
  Int a = 0;
  Int b = 0;
  Int c = 0;

  while(a < blength)
  {
    if(aa[a] >= 0) {
      bb[b] = aa[a];
      b = b + 1;
      a = a + 1;
    } else {
      a = a + 1;
    }
  }

  a = 0;
  while(a < blength)
  {
    if(aa[a] < 0) {
      cc[c] = aa[a];
      c = c + 1;
      a = a + 1;
    } else {
      a = a + 1;
    }
  }
}

(conjecture
  (forall ((x Int))
    (=>
      (and
        (> blength 0)
        (< x (b main_end))
      )
      (>= (bb main_end x) 0)
    )
  )
)
