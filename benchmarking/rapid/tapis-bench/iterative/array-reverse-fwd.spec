func main()
{
	const Int[] b;
	const Int blength;
	Int[] a;

	Int i = 0;
	while(i < blength)
	{
		a[i] = b[blength - i - 1];
		i = i + 1;
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
			(= (a main_end j) (b (- blength (+ j 1))))
		)
	)
)
