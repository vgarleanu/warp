//! Test utilities to test your filters.
//!
//! [`Filter`](../trait.Filter.html)s can be easily tested without starting up an HTTP
//! server, by making use of the [`RequestBuilder`](./struct.RequestBuilder.html) in this
//! module.
//!
//! # Testing Filters
//!
//! It's easy to test filters, especially if smaller filters are used to build
//! up your full set. Consider these example filters:
//!
//! ```
//! use warp::Filter;
//!
//! fn sum() -> impl Filter<Extract = (u32,), Error = warp::Rejection> + Copy {
//!     warp::path::param()
//!         .and(warp::path::param())
//!         .map(|x: u32, y: u32| {
//!             x + y
//!         })
//! }
//!
//! fn math() -> impl Filter<Extract = (String,), Error = warp::Rejection> + Copy {
//!     warp::post()
//!         .and(sum())
//!         .map(|z: u32| {
//!             format!("Sum = {}", z)
//!         })
//! }
//! ```
//!
//! We can test some requests against the `sum` filter like this:
//!
//! ```
//! # use warp::Filter;
//! #[tokio::test]
//! async fn test_sum() {
//! #    let sum = || warp::any().map(|| 3);
//!     let filter = sum();
//!
//!     // Execute `sum` and get the `Extract` back.
//!     let value = warp::test::request()
//!         .path("/1/2")
//!         .filter(&filter)
//!         .await
//!         .unwrap();
//!     assert_eq!(value, 3);
//!
//!     // Or simply test if a request matches (doesn't reject).
//!     assert!(
//!         warp::test::request()
//!             .path("/1/-5")
//!             .matches(&filter)
//!             .await
//!     );
//! }
//! ```
//!
//! If the filter returns something that implements `Reply`, and thus can be
//! turned into a response sent back to the client, we can test what exact
//! response is returned. The `math` filter uses the `sum` filter, but returns
//! a `String` that can be turned into a response.
//!
//! ```
//! # use warp::Filter;
//! #[test]
//! fn test_math() {
//! #    let math = || warp::any().map(warp::reply);
//!     let filter = math();
//!
//!     let res = warp::test::request()
//!         .path("/1/2")
//!         .reply(&filter);
//!     assert_eq!(res.status(), 405, "GET is not allowed");
//!
//!     let res = warp::test::request()
//!         .method("POST")
//!         .path("/1/2")
//!         .reply(&filter);
//!     assert_eq!(res.status(), 200);
//!     assert_eq!(res.body(), "Sum is 3");
//! }
//! ```
use std::convert::TryFrom;
use std::future::Future;
use std::net::SocketAddr;

use bytes::Bytes;
use futures_util::future;
use futures_util::FutureExt;
use http::{
    header::{HeaderName, HeaderValue},
    Response,
};
use serde::Serialize;
use serde_json;

use crate::filter::Filter;
use crate::reject::IsReject;
use crate::reply::Reply;
use crate::route::{self, Route};
use crate::Request;

use self::inner::OneOrTuple;

/// Starts a new test `RequestBuilder`.
pub fn request() -> RequestBuilder {
    RequestBuilder {
        remote_addr: None,
        req: Request::default(),
    }
}

/// A request builder for testing filters.
///
/// See [module documentation](crate::test) for an overview.
#[must_use = "RequestBuilder does nothing on its own"]
#[derive(Debug)]
pub struct RequestBuilder {
    remote_addr: Option<SocketAddr>,
    req: Request,
}

impl RequestBuilder {
    /// Sets the method of this builder.
    ///
    /// The default if not set is `GET`.
    ///
    /// # Example
    ///
    /// ```
    /// let req = warp::test::request()
    ///     .method("POST");
    /// ```
    ///
    /// # Panic
    ///
    /// This panics if the passed string is not able to be parsed as a valid
    /// `Method`.
    pub fn method(mut self, method: &str) -> Self {
        *self.req.method_mut() = method.parse().expect("valid method");
        self
    }

    /// Sets the request path of this builder.
    ///
    /// The default is not set is `/`.
    ///
    /// # Example
    ///
    /// ```
    /// let req = warp::test::request()
    ///     .path("/todos/33");
    /// ```
    ///
    /// # Panic
    ///
    /// This panics if the passed string is not able to be parsed as a valid
    /// `Uri`.
    pub fn path(mut self, p: &str) -> Self {
        let uri = p.parse().expect("test request path invalid");
        *self.req.uri_mut() = uri;
        self
    }

    /// Set a header for this request.
    ///
    /// # Example
    ///
    /// ```
    /// let req = warp::test::request()
    ///     .header("accept", "application/json");
    /// ```
    ///
    /// # Panic
    ///
    /// This panics if the passed strings are not able to be parsed as a valid
    /// `HeaderName` and `HeaderValue`.
    pub fn header<K, V>(mut self, key: K, value: V) -> Self
    where
        HeaderName: TryFrom<K>,
        HeaderValue: TryFrom<V>,
    {
        let name: HeaderName = TryFrom::try_from(key)
            .map_err(|_| ())
            .expect("invalid header name");
        let value = TryFrom::try_from(value)
            .map_err(|_| ())
            .expect("invalid header value");
        self.req.headers_mut().insert(name, value);
        self
    }

    /// Set the remote address of this request
    ///
    /// Default is no remote address.
    ///
    /// # Example
    /// ```
    /// use std::net::{IpAddr, Ipv4Addr, SocketAddr};
    ///
    /// let req = warp::test::request()
    ///     .remote_addr(SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080));
    /// ```
    pub fn remote_addr(mut self, addr: SocketAddr) -> Self {
        self.remote_addr = Some(addr);
        self
    }

    /// Add a type to the request's `http::Extensions`.
    pub fn extension<T>(mut self, ext: T) -> Self
    where
        T: Send + Sync + 'static,
    {
        self.req.extensions_mut().insert(ext);
        self
    }

    /// Set the bytes of this request body.
    ///
    /// Default is an empty body.
    ///
    /// # Example
    ///
    /// ```
    /// let req = warp::test::request()
    ///     .body("foo=bar&baz=quux");
    /// ```
    pub fn body(mut self, body: impl AsRef<[u8]>) -> Self {
        let body = body.as_ref().to_vec();
        let len = body.len();
        *self.req.body_mut() = body.into();
        self.header("content-length", len.to_string())
    }

    /// Set the bytes of this request body by serializing a value into JSON.
    ///
    /// # Example
    ///
    /// ```
    /// let req = warp::test::request()
    ///     .json(&true);
    /// ```
    pub fn json(mut self, val: &impl Serialize) -> Self {
        let vec = serde_json::to_vec(val).expect("json() must serialize to JSON");
        let len = vec.len();
        *self.req.body_mut() = vec.into();
        self.header("content-length", len.to_string())
            .header("content-type", "application/json")
    }

    /// Tries to apply the `Filter` on this request.
    ///
    /// # Example
    ///
    /// ```no_run
    /// async {
    ///     let param = warp::path::param::<u32>();
    ///
    ///     let ex = warp::test::request()
    ///         .path("/41")
    ///         .filter(&param)
    ///         .await
    ///         .unwrap();
    ///
    ///     assert_eq!(ex, 41);
    ///
    ///     assert!(
    ///         warp::test::request()
    ///             .path("/foo")
    ///             .filter(&param)
    ///             .await
    ///             .is_err()
    ///     );
    ///};
    /// ```
    pub async fn filter<F>(self, f: &F) -> Result<<F::Extract as OneOrTuple>::Output, F::Error>
    where
        F: Filter,
        F::Future: Send + 'static,
        F::Extract: OneOrTuple + Send + 'static,
        F::Error: Send + 'static,
    {
        self.apply_filter(f).await.map(|ex| ex.one_or_tuple())
    }

    /// Returns whether the `Filter` matches this request, or rejects it.
    ///
    /// # Example
    ///
    /// ```no_run
    /// async {
    ///     let get = warp::get();
    ///     let post = warp::post();
    ///
    ///     assert!(
    ///         warp::test::request()
    ///             .method("GET")
    ///             .matches(&get)
    ///             .await
    ///     );
    ///
    ///     assert!(
    ///         !warp::test::request()
    ///             .method("GET")
    ///             .matches(&post)
    ///             .await
    ///     );
    ///};
    /// ```
    pub async fn matches<F>(self, f: &F) -> bool
    where
        F: Filter,
        F::Future: Send + 'static,
        F::Extract: Send + 'static,
        F::Error: Send + 'static,
    {
        self.apply_filter(f).await.is_ok()
    }

    /// Returns `Response` provided by applying the `Filter`.
    ///
    /// This requires that the supplied `Filter` return a [`Reply`](Reply).
    pub async fn reply<F>(self, f: &F) -> Response<Bytes>
    where
        F: Filter + 'static,
        F::Extract: Reply + Send,
        F::Error: IsReject + Send,
    {
        // TODO: de-duplicate this and apply_filter()
        assert!(!route::is_set(), "nested test filter calls");

        let route = Route::new(self.req, self.remote_addr);
        let mut fut = Box::pin(route::set(&route, move || {
            f.filter(crate::filter::Internal).then(|result| async {
                let res = match result {
                    Ok(rep) => rep.into_response(),
                    Err(rej) => {
                        tracing::debug!("rejected: {:?}", rej);
                        rej.into_response()
                    }
                };
                let (parts, body) = res.into_parts();

                Response::from_parts(parts, body)
            })
        }));

        let fut = future::poll_fn(move |cx| route::set(&route, || fut.as_mut().poll(cx)));

        fut.await
    }

    fn apply_filter<F>(self, f: &F) -> impl Future<Output = Result<F::Extract, F::Error>>
    where
        F: Filter,
        F::Future: Send + 'static,
        F::Extract: Send + 'static,
        F::Error: Send + 'static,
    {
        assert!(!route::is_set(), "nested test filter calls");

        let route = Route::new(self.req, self.remote_addr);
        let mut fut = Box::pin(route::set(&route, move || {
            f.filter(crate::filter::Internal)
        }));
        future::poll_fn(move |cx| route::set(&route, || fut.as_mut().poll(cx)))
    }
}

mod inner {
    pub trait OneOrTuple {
        type Output;

        fn one_or_tuple(self) -> Self::Output;
    }

    impl OneOrTuple for () {
        type Output = ();
        fn one_or_tuple(self) -> Self::Output {}
    }

    macro_rules! one_or_tuple {
        ($type1:ident) => {
            impl<$type1> OneOrTuple for ($type1,) {
                type Output = $type1;
                fn one_or_tuple(self) -> Self::Output {
                    self.0
                }
            }
        };
        ($type1:ident, $( $type:ident ),*) => {
            one_or_tuple!($( $type ),*);

            impl<$type1, $($type),*> OneOrTuple for ($type1, $($type),*) {
                type Output = Self;
                fn one_or_tuple(self) -> Self::Output {
                    self
                }
            }
        }
    }

    one_or_tuple! {
        T1,
        T2,
        T3,
        T4,
        T5,
        T6,
        T7,
        T8,
        T9,
        T10,
        T11,
        T12,
        T13,
        T14,
        T15,
        T16
    }
}
