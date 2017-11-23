
extern crate urlencoding;

use urlencoding::{encode, decode};
use std::iter::Iterator;

/// A query string. Holds a list of `Param`s.
///
/// Examples
///
/// Parameters are indexed by their names.
///
/// ```
/// let qs = qstring::QString::from("?foo=bar%20baz");
/// let foo = qs["foo"].clone().unwrap();
/// assert_eq!(foo, "bar baz");
/// ```
///
/// Parameters not found are None.
///
/// ```
/// let qs = qstring::QString::from("?foo=bar");
/// let foo = &qs["panda"];
/// assert!(foo.is_none());
/// ```
///
/// The query string can be assembled.
///
/// ```
/// let qs = qstring::QString::new(vec![
///    qstring::Param::new("foo", "bar baz"),
///    qstring::Param::new("panda", "true"),
/// ]);
/// assert_eq!(format!("{}", qs), "?&foo=bar%20baz&panda=true");
/// ```
///
/// Can be looped over as `Param`.
///
/// ```
/// let qs = qstring::QString::from("?foo=bar");
/// for param in qs {
///    assert_eq!(param.name, "foo");
///    assert_eq!(param.value, "bar");
///    assert_eq!(param, ("foo", "bar"));
/// }
/// ```
#[derive(Clone, Debug, PartialEq)]
pub struct QString {
    /// List of parameters in the query string.
    keys: Vec<String>,
    vals: Vec<Option<String>>,
    empty: Option<String>,
}

/// Parameter found in a query string.
#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    /// Query parameter name.
    pub name: String,
    /// Query parameter value.
    pub value: String,
}

/// Single parameter in a query string.
impl Param {

    /// Constructs a `Param` from raw `&str` values.
    ///
    /// ```
    /// let p = qstring::Param::new("foo", "bar baz");
    /// assert_eq!(format!("{}", p), "&foo=bar%20baz")
    /// ```
    pub fn new(name: &str, value: &str) -> Param {
        Param {
            name: name.to_string(),
            value: value.to_string(),
        }
    }

    /// Constructs a `Param` by URL decoding the given values.
    ///
    /// ```
    /// let p = qstring::Param::new_esc("foo", "bar%20baz");
    /// assert_eq!(format!("{}", p), "&foo=bar%20baz")
    /// ```
    pub fn new_esc(name: &str, value: &str) -> Param {
        Param {
            name: decode(name).unwrap_or_else(|_| name.to_string()),
            value: decode(value).unwrap_or_else(|_| value.to_string()),
        }
    }

}

impl QString {

    /// Constructs a `QString` from a list of `Param`s.
    ///
    /// ```
    /// let qs = qstring::QString::new(vec![
    ///    qstring::Param::new("foo", "bar baz"),
    ///    qstring::Param::new("panda", "true"),
    /// ]);
    /// assert_eq!(format!("{}", qs), "?&foo=bar%20baz&panda=true");
    /// ```
    pub fn new(params: Vec<Param> ) -> QString {
        QString {
            keys: params.iter().map(|p| p.name.clone()).collect(),
            vals: params.into_iter().map(|p| Some(p.value)).collect(),
            empty: None,
        }
    }

    /// Get a query parameter by name.
    ///
    /// ```
    /// let qs = qstring::QString::from("?foo=bar");
    /// let foo = qs.get("foo");
    /// assert_eq!(foo, Some("bar".to_string()));
    /// ```
    pub fn get(&self, name: &str) -> Option<String> {
        let idx = self.keys.iter().position(|k| k == name)?;
        self.vals[idx].clone()
    }

}

impl<'a> From<&'a str> for QString {

    /// Constructs a new `QString` and find the `Param`s therein.
    ///
    /// Examples
    ///
    /// ```
    /// let qs = qstring::QString::from("?foo=bar");
    /// let v: Vec<qstring::Param> = qs.into();
    /// assert_eq!(v, vec![("foo", "bar")]);
    /// ```
    fn from(origin: &str) -> Self {

        // current slice left to find params in
        let mut cur = origin;

        // move forward if start with ?
        if cur.len() > 0 && &cur[0..1] == "?" {
            cur = &cur[1..];
        }

        // where we build found parameters into
        let mut params = vec![];

        while cur.len() > 0 {
            // if we're positioned on a &, skip it
            if &cur[0..1] == "&" {
                cur = &cur[1..];
                continue;
            }
            // find position of next =
            let (name, rest) = match cur.find("=") {
                // no next =, name will be until next & or until end
                None => match cur.find("&") {
                    // no &, name is until end
                    None => (cur, ""),
                    // name is until next &, which means no value and shortcut
                    // to start straight after the &.
                    Some(pos) => {
                        params.push(Param::new_esc(&cur[..pos], ""));
                        cur = &cur[(pos + 1)..];
                        continue;
                    },
                },
                // found one, name is up until = and rest is after.
                Some(pos) => (&cur[..pos], &cur[(pos + 1)..]),
            };
            // skip parameters with no name
            if name.len() == 0 {
                cur = rest;
                continue;
            }
            // from rest, find next occurence of &
            let (value, newcur) = match rest.find("&") {
                // no next &, then value is all up until end
                None => (rest, ""),
                // found one, value is up until & and next round starts after.
                Some(pos) => (&rest[..pos], &rest[(pos + 1)..]),
            };
            // found a parameter
            params.push(Param::new_esc(name, value));
            cur = newcur;
        }

        QString::new(params)
    }

}

impl Into<Vec<Param>> for QString {
    fn into(self) -> Vec<Param> {
        self.keys.iter().enumerate()
        .map(|(idx, k)| Param {
            name:k.clone(),
            value:self.vals[idx].clone().unwrap()
        })
        .collect()
    }
}

impl IntoIterator for QString {
    type Item = Param;
    type IntoIter = ::std::vec::IntoIter<Param>;
    fn into_iter(self) -> Self::IntoIter {
        let v:Vec<Param> = self.into();
        v.into_iter()
    }
}


impl<'a> PartialEq<(&'a str, &'a str)> for Param {
    fn eq(&self, other: &(&str, &str)) -> bool {
        self.name == other.0 && self.value == other.1
    }
}

impl ::std::fmt::Display for Param {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "&{}={}", encode(&self.name), encode(&self.value))
    }
}

impl<'b> ::std::ops::Index<&'static str> for QString {
    type Output = Option<String>;
    fn index<'a>(&'a self, index: &'b str) -> &'a Self::Output {
        let idx = self.keys.iter()
            .rev()
            .position(|k| k == index);
        let ret = match idx {
            None => &self.empty,
            Some(idx) => self.vals.index(idx),
        };
        ret
    }
}

impl ::std::fmt::Display for QString {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "?")?;
        let v: Vec<Param> = self.clone().into();
        for param in v {
            write!(f, "{}", param)?;
        }
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test {
        ($func_name:ident, $origin:expr, $result:expr) => (
            #[test]
            fn $func_name() {
                let qs = QString::from($origin);
                let ps: Vec<Param> = qs.into();
                assert_eq!(ps, $result as Vec<(&str, &str)>);
            }
        )
    }

    test!(empty_1, "", vec![]);
    test!(empty_2, "?", vec![]);
    test!(empty_3, "&", vec![]);
    test!(empty_4, "=", vec![]);
    test!(empty_5, "?=", vec![]);
    test!(empty_6, "?&", vec![]);

    test!(a_is_1, "a", vec![("a", "")]);
    test!(a_is_2, "a=", vec![("a", "")]);
    test!(a_is_3, "a=b", vec![("a", "b")]);
    test!(a_is_4, "?a", vec![("a", "")]);
    test!(a_is_5, "?a=", vec![("a", "")]);
    test!(a_is_6, "?a=b", vec![("a", "b")]);
    test!(a_is_7, "?&a", vec![("a", "")]);
    test!(a_is_8, "?&a=", vec![("a", "")]);
    test!(a_is_9, "?&a=b", vec![("a", "b")]);
    test!(a_is_10, "?a=&", vec![("a", "")]);
    test!(a_is_11, "?=a", vec![("a", "")]);

    test!(a_is_eq_1, "a==", vec![("a", "=")]);

    test!(is_q_1, "??", vec![("?", "")]);
    test!(is_q_2, "&?", vec![("?", "")]);
    test!(is_q_3, "??a", vec![("?a", "")]);
    test!(is_q_4, "&?a", vec![("?a", "")]);

    test!(ac_is_1, "?a&c", vec![("a", ""), ("c", "")]);
    test!(ac_is_2, "?a&c&", vec![("a", ""), ("c", "")]);
    test!(ac_is_3, "?a=&c", vec![("a", ""), ("c", "")]);
    test!(ac_is_4, "?a=&c=", vec![("a", ""), ("c", "")]);
    test!(ac_is_5, "?a=b&c=", vec![("a", "b"), ("c", "")]);
    test!(ac_is_6, "?a=&c=d", vec![("a", ""), ("c", "d")]);
    test!(ac_is_7, "?a=b&c=d", vec![("a", "b"), ("c", "d")]);

}
