func main()
{
	const Int[] b;
	const Int blength;
	const Int v;

    Int k = blength;
    Int idx = 1-2;
	while(k > 0)
	{
        if(b[k - 1] == v) {
            idx = k - 1;
        } else {
            skip;
        }
		k = k - 1;
	}
}

(conjecture
        (=>
        (> blength 0)
		(=>
			(not
			    (=
			        (idx main_end)
			        (- 1 2)))
			(=
			    (b (idx main_end))
			    v)
		)
		)
)
