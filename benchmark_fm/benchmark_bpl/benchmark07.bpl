type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, s, t, u3, u5, v2, v4, v6, x, y, z: A;

	x := y;

	if (s == v6) {
		x := t;
		y := k;
		assume(t == k);
		while (y != z){
			x := f(x);
			y := f(y);
			z := f(z);
		}
	} else {
		x := f(x);
		y := f(y);
	}

	if (s == v2) {
		x := f(t);
		y := f(k);
		x := h(x);
		y := h(y);
		assume(t == k);
	} else {
			if (s == u3) {
				x := f(x);
				y := f(y);
				x := h(x);
				y := h(y);
			}
	}

	if (s == u5) {
		x := t;
		y := k;
		while (y != z){
			x := f(x);
			y := f(y);
			z := f(z);
		}
		assume(t == k);
	} else {
			if (s == v4) {
				x := f(x);
				x := h(x);
				y := f(y);
				y := h(y);
			}
	}

	assert(x == y);
}