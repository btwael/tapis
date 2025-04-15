func main()
{
	const Int[] b;
	const Int blength;
	Int[] a;

	Int i = 0;
    Int k = blength;
	while(i < blength && k > 0 && i <= k)
	{
		a[i] = b[i];
		a[k - 1] = b[k - 1];
		i = i + 1;
		k = k - 1;
	}
}

(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 blength)
				(<= 0 j)
				(< j blength)
			)
			(= (a main_end j) (b j))
		)
	)
)
