// Package result is the railway type of Go+: a computation that either
// produced a value (Ok) or failed (Err). It is authored in Go+ and
// distributed as generated Go — consumers never need the goplus toolchain.
package result

// Result carries one success value or one failure value.
type Result[T any, E error] enum {
	Ok(value T)
	Err(err E)
}

// Of enters the railway from a Go-shaped pair.
func Of[T any](v T, err error) Result[T, error] {
	if err != nil {
		return Err[T, error](err)
	}
	return Ok[T, error](v)
}

// Bind connects a switch function onto the railway: applied to the Ok
// value; an Err bypasses it.
func (r Result[T, E]) Bind[U any](f func(T) Result[U, E]) Result[U, E] {
	match r {
	case Ok(v):
		return f(v)
	case Err(e):
		return Err[U, E](e)
	}
}

// Map lifts a plain function onto the success track.
func (r Result[T, E]) Map[U any](f func(T) U) Result[U, E] {
	match r {
	case Ok(v):
		return Ok[U, E](f(v))
	case Err(e):
		return Err[U, E](e)
	}
}

// MapError transforms the failure track.
func (r Result[T, E]) MapError[F error](f func(E) F) Result[T, F] {
	match r {
	case Ok(v):
		return Ok[T, F](v)
	case Err(e):
		return Err[T, F](f(e))
	}
}

// Tee runs a dead-end function on the Ok value and passes the Result
// through unchanged; an Err bypasses it.
func (r Result[T, E]) Tee(f func(T)) Result[T, E] {
	match r {
	case Ok(v):
		f(v)
	case Err(_):
	}
	return r
}

// Unpack leaves the railway in Go shape: Ok yields (value, nil); Err
// yields (zero, err).
func (r Result[T, E]) Unpack() (T, error) {
	match r {
	case Ok(v):
		return v, nil
	case Err(e):
		var zero T
		return zero, e
	}
}

// UnwrapOr yields the Ok value or a fallback.
func (r Result[T, E]) UnwrapOr(fallback T) T {
	match r {
	case Ok(v):
		return v
	case Err(_):
		return fallback
	}
}

// IsOk reports whether the Result is on the success track.
func (r Result[T, E]) IsOk() bool {
	match r {
	case Ok(_):
		return true
	case Err(_):
		return false
	}
}

// IsErr reports whether the Result is on the failure track.
func (r Result[T, E]) IsErr() bool {
	match r {
	case Ok(_):
		return false
	case Err(_):
		return true
	}
}
