
extern crate percent_encoding;

use percent_encoding::{percent_decode, utf8_percent_encode, QUERY_ENCODE_SET};
use std::iter::Iterator;

/// A query string. Holds a list of `(key,value)`.
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
/// Parameters not found are `None`.
///
/// ```
/// let qs = qstring::QString::from("?foo=bar");
/// let foo = &qs["panda"];
/// assert!(foo.is_none());
/// ```
///
/// The query string can be assembled from pairs.
///
/// ```
/// let qs = qstring::QString::new(vec![
///    ("foo", "bar baz"),
///    ("panda", "true"),
/// ]);
/// assert_eq!(format!("{}", qs), "?foo=bar%20baz&panda=true");
/// ```
///
#[derive(Clone, Debug, PartialEq)]
pub struct QString {
    keys: Vec<String>,
    vals: Vec<Option<String>>,
    empty: Option<String>,
}

impl QString {

    /// Constructs a `QString` from a list of pairs.
    ///
    /// ```
    /// let qs = qstring::QString::new(vec![
    ///    ("foo", "bar baz"),
    ///    ("panda", "true"),
    /// ]);
    /// assert_eq!(format!("{}", qs), "?foo=bar%20baz&panda=true");
    /// ```
    pub fn new<S>(params: Vec<(S, S)> ) -> QString
        where S: Into<String> {
        let mut keys = vec![];
        let mut vals = vec![];
        for (k, v) in params {
            keys.push(k.into());
            vals.push(Some(v.into()));
        }
        QString {
            keys,
            vals,
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

    /// Converts the QString to list of pairs.
    ///
    /// ```
    /// let qs = qstring::QString::from("?foo=bar&baz=boo");
    /// let ps = qs.to_pairs();
    /// assert_eq!(ps, vec![
    ///     ("foo".to_string(), "bar".to_string()),
    ///     ("baz".to_string(), "boo".to_string()),
    /// ]);
    /// ```
    pub fn to_pairs(self) -> Vec<(String, String)> {
        let v: Vec<String> = self.vals
            .into_iter()
            .map(|v| v.unwrap())
            .collect();
        let ret: Vec<(String,String)> =  self.keys
            .into_iter()
            .zip(v.into_iter())
            .collect();
        ret
    }

}

impl<'a> From<&'a str> for QString {

    /// Constructs a new `QString` by parsing a query string part of the URL.
    /// Can start with ? or not, either works.
    ///
    /// Examples
    ///
    /// ```
    /// let qs = qstring::QString::from("?foo=bar");
    /// let v: Vec<(String, String)> = qs.to_pairs();
    /// assert_eq!(v, vec![("foo".to_string(), "bar".to_string())]);
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
                        params.push((decode(&cur[..pos]), "".to_string()));
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
            params.push((decode(name), decode(value)));
            cur = newcur;
        }

        QString::new(params)
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

impl IntoIterator for QString {
    type Item = (String, String);
    type IntoIter = ::std::vec::IntoIter<(String,String)>;
    fn into_iter(self) -> Self::IntoIter {
        self.to_pairs().into_iter()
    }
}

impl ::std::fmt::Display for QString {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "?")?;
        for (idx, k) in self.keys.iter().enumerate() {
            let v = self.vals[idx].as_ref().unwrap();
            write!(f, "{}{}={}", (if idx == 0 {""} else {"&"}), encode(k), encode(v))?;
        }
        Ok(())
    }
}


fn decode(s: &str) -> String {
    percent_decode(s.as_bytes())
        .decode_utf8()
        .map(|cow| cow.into_owned())
        .unwrap_or_else(|_| s.to_string())
}


fn encode(s: &str) -> String {
    utf8_percent_encode(s, QUERY_ENCODE_SET).to_string()
}


#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! test {
        ($func_name:ident, $origin:expr, $result:expr) => (
            #[test]
            fn $func_name() {
                let qs = QString::from($origin);
                let ps: Vec<(String, String)> = qs.to_pairs();
                let cs: Vec<(String, String)> = ($result as Vec<(&str, &str)>)
                    .into_iter().map(|(k,v)| (k.to_string(), v.to_string()))
                    .collect();
                assert_eq!(ps, cs);
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
