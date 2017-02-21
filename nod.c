/*@ predicate is_divisor(int m, int n) =
       m ? n % m == 0 : \false;
*/

/*@ predicate is_gcd(int z, int x1, int x2) =
	   is_divisor(z, x1)
	&& is_divisor(z, x2)
	&& \forall int i; is_divisor(i, x1) && is_divisor(i, x2) ==> (i <= z);
 */

/*@ requires (x1 > 0) && (x2 > 0);
    ensures is_gcd(\result, x1, x2);
 */
int nod(int x1, int x2)
{
	int y1 = x1;
	int y2 = x2;
	int tmp = 0;

	if (y1 > y2) {
		y1 = x2;
		y2 = x1;
	}
    /*@ requires y1 != 0;
        ensures y1 == 0;
        assigns y1, y2;
        //assert \forall integer i; 0 <= i < n ==> tmp == y1; y1 == y2 % y1; y2 = tmp;
     */
	while (y1 != 0) {
		tmp = y1;
		y1 = y2 % y1;
		y2 = tmp;
	}
}
