type A;
function f(x: A) returns (A);
function h(x: A) returns (A);
procedure main(){

	var k, s, t, u1, v4, x, y: A;

	x := y;

	if (s == u1) {
		x := f(t);
		y := f(k);
		assume(t == k);
		x := h(x);
		y := h(y);
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