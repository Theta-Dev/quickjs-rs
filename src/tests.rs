use std::collections::HashMap;

use super::*;

// #[test]
// fn test_global_properties() {
//     let c = Context::new().unwrap();

//     assert_eq!(
//         c.global_property("lala"),
//         Err(ExecutionError::Exception(
//             "Global object does not have property 'lala'".into()
//         ))
//     );

//     c.set_global_property("testprop", true).unwrap();
//     assert_eq!(
//         c.global_property("testprop").unwrap(),
//         JsValue::Bool(true),
//     );
// }

#[test]
fn test_eval_pass() {
    use std::iter::FromIterator;

    let c = Context::new().unwrap();

    let cases = vec![
        ("undefined", Ok(JsValue::Undefined)),
        ("null", Ok(JsValue::Null)),
        ("true", Ok(JsValue::Bool(true))),
        ("2 > 10", Ok(JsValue::Bool(false))),
        ("1", Ok(JsValue::Int(1))),
        ("1 + 1", Ok(JsValue::Int(2))),
        ("1.1", Ok(JsValue::Float(1.1))),
        ("2.2 * 2 + 5", Ok(JsValue::Float(9.4))),
        ("\"abc\"", Ok(JsValue::String("abc".into()))),
        (
            "[1,2]",
            Ok(JsValue::Array(vec![JsValue::Int(1), JsValue::Int(2)])),
        ),
    ];

    for (code, res) in cases.into_iter() {
        assert_eq!(c.eval(code), res,);
    }

    let obj_cases = vec![
        (
            r#" {"a": null, "b": undefined} "#,
            Ok(JsValue::Object(HashMap::from_iter(vec![
                ("a".to_string(), JsValue::Null),
                ("b".to_string(), JsValue::Undefined),
            ]))),
        ),
        (
            r#" {a: 1, b: true, c: {c1: false}} "#,
            Ok(JsValue::Object(HashMap::from_iter(vec![
                ("a".to_string(), JsValue::Int(1)),
                ("b".to_string(), JsValue::Bool(true)),
                (
                    "c".to_string(),
                    JsValue::Object(HashMap::from_iter(vec![(
                        "c1".to_string(),
                        JsValue::Bool(false),
                    )])),
                ),
            ]))),
        ),
    ];

    for (index, (code, res)) in obj_cases.into_iter().enumerate() {
        let full_code = format!("var v{index} = {code}; v{index}");
        assert_eq!(c.eval(&full_code), res,);
    }

    assert_eq!(c.eval_as::<bool>("true").unwrap(), true,);
    assert_eq!(c.eval_as::<i32>("1 + 2").unwrap(), 3,);

    let value: String = c.eval_as("var x = 44; x.toString()").unwrap();
    assert_eq!(&value, "44");

    #[cfg(feature = "bigint")]
    assert_eq!(
        c.eval_as::<num_bigint::BigInt>("1n << 100n").unwrap(),
        num_bigint::BigInt::from(1i128 << 100)
    );

    #[cfg(feature = "bigint")]
    assert_eq!(c.eval_as::<i64>("1 << 30").unwrap(), 1i64 << 30);

    #[cfg(feature = "bigint")]
    assert_eq!(c.eval_as::<u128>("1n << 100n").unwrap(), 1u128 << 100);
}

#[test]
fn test_eval_syntax_error() {
    let c = Context::new().unwrap();
    assert_eq!(
        c.eval(
            r#"
            !!!!
        "#
        ),
        Err(ExecutionError::Exception(
            "SyntaxError: unexpected token in expression: \'\'".into()
        ))
    );
}

#[test]
fn test_eval_exception() {
    let c = Context::new().unwrap();
    assert_eq!(
        c.eval(
            r#"
            function f() {
                throw new Error("My Error");
            }
            f();
        "#
        ),
        Err(ExecutionError::Exception("Error: My Error".into(),))
    );
}

#[test]
fn eval_async() {
    let c = Context::new().unwrap();

    let value = c
        .eval(
            r#"
        new Promise((resolve, _) => {
            resolve(33);
        })
    "#,
        )
        .unwrap();
    assert_eq!(value, JsValue::Int(33));

    let res = c.eval(
        r#"
        new Promise((_resolve, reject) => {
            reject("Failed...");
        })
    "#,
    );
    assert_eq!(
        res,
        Err(ExecutionError::Exception(JsValue::String(
            "Failed...".into()
        )))
    );
}

#[test]
fn test_set_global() {
    let context = Context::new().unwrap();
    context.set_global("someGlobalVariable", 42).unwrap();
    let value = context.eval_as::<i32>("someGlobalVariable").unwrap();
    assert_eq!(value, 42,);
}

#[test]
fn test_call() {
    let c = Context::new().unwrap();

    assert_eq!(
        c.call_function("parseInt", vec!["22"]).unwrap(),
        JsValue::Int(22),
    );

    c.eval(
        r#"
        function add(a, b) {
            return a + b;
        }
    "#,
    )
    .unwrap();
    assert_eq!(
        c.call_function("add", vec![5, 7]).unwrap(),
        JsValue::Int(12),
    );

    c.eval(
        r#"
        function sumArray(arr) {
            let sum = 0;
            for (const value of arr) {
                sum += value;
            }
            return sum;
        }
    "#,
    )
    .unwrap();
    assert_eq!(
        c.call_function("sumArray", vec![vec![1, 2, 3]]).unwrap(),
        JsValue::Int(6),
    );

    c.eval(
        r#"
        function addObject(obj) {
            let sum = 0;
            for (const key of Object.keys(obj)) {
                sum += obj[key];
            }
            return sum;
        }
    "#,
    )
    .unwrap();
    let mut obj = std::collections::HashMap::<String, i32>::new();
    obj.insert("a".into(), 10);
    obj.insert("b".into(), 20);
    obj.insert("c".into(), 30);
    assert_eq!(
        c.call_function("addObject", vec![obj]).unwrap(),
        JsValue::Int(60),
    );
}

#[test]
fn test_call_large_string() {
    let c = Context::new().unwrap();
    c.eval(" function strLen(s) { return s.length; } ").unwrap();

    let s = " ".repeat(200_000);
    let v = c.call_function("strLen", vec![s]).unwrap();
    assert_eq!(v, JsValue::Int(200_000));
}

#[test]
fn call_async() {
    let c = Context::new().unwrap();

    c.eval(
        r#"
        function asyncOk() {
            return new Promise((resolve, _) => {
                resolve(33);
            });
        }

        function asyncErr() {
            return new Promise((_resolve, reject) => {
                reject("Failed...");
            });
        }
    "#,
    )
    .unwrap();

    let value = c.call_function("asyncOk", vec![true]).unwrap();
    assert_eq!(value, JsValue::Int(33));

    let res = c.call_function("asyncErr", vec![true]);
    assert_eq!(
        res,
        Err(ExecutionError::Exception(JsValue::String(
            "Failed...".into()
        )))
    );
}

#[test]
fn test_callback() {
    let c = Context::new().unwrap();

    c.add_callback("no_arguments", || true).unwrap();
    assert_eq!(c.eval_as::<bool>("no_arguments()").unwrap(), true);

    c.add_callback("cb1", |flag: bool| !flag).unwrap();
    assert_eq!(c.eval("cb1(true)").unwrap(), JsValue::Bool(false),);

    c.add_callback("concat2", |a: String, b: String| format!("{a}{b}"))
        .unwrap();
    assert_eq!(
        c.eval(r#"concat2("abc", "def")"#).unwrap(),
        JsValue::String("abcdef".into()),
    );

    c.add_callback("add2", |a: i32, b: i32| -> i32 { a + b })
        .unwrap();
    assert_eq!(c.eval("add2(5, 11)").unwrap(), JsValue::Int(16),);

    c.add_callback("sum", |items: Vec<i32>| -> i32 { items.iter().sum() })
        .unwrap();
    assert_eq!(c.eval("sum([1, 2, 3, 4, 5, 6])").unwrap(), JsValue::Int(21),);

    c.add_callback("identity", |value: JsValue| -> JsValue { value })
        .unwrap();
    {
        let v = JsValue::from(22);
        assert_eq!(c.eval("identity(22)").unwrap(), v);
    }
}

#[test]
fn test_callback_argn_variants() {
    macro_rules! callback_argn_tests {
        [
            $(
                $len:literal : ( $( $argn:ident : $argv:literal ),* ),
            )*
        ] => {
            $(
                {
                    // Test plain return type.
                    let name = format!("cb{}", $len);
                    let c = Context::new().unwrap();
                    c.add_callback(&name, | $( $argn : i32 ),*| -> i32 {
                        $( $argn + )* 0
                    }).unwrap();

                    let code = format!("{}( {} )", name, "1,".repeat($len));
                    let v = c.eval(&code).unwrap();
                    assert_eq!(v, JsValue::Int($len));

                    // Test Result<T, E> return type with OK(_) returns.
                    let name = format!("cbres{}", $len);
                    c.add_callback(&name, | $( $argn : i32 ),*| -> Result<i32, String> {
                        Ok($( $argn + )* 0)
                    }).unwrap();

                    let code = format!("{}( {} )", name, "1,".repeat($len));
                    let v = c.eval(&code).unwrap();
                    assert_eq!(v, JsValue::Int($len));

                    // Test Result<T, E> return type with Err(_) returns.
                    let name = format!("cbreserr{}", $len);
                    c.add_callback(&name, #[allow(unused_variables)] | $( $argn : i32 ),*| -> Result<i32, String> {
                        Err("error".into())
                    }).unwrap();

                    let code = format!("{}( {} )", name, "1,".repeat($len));
                    let res = c.eval(&code);
                    assert_eq!(res, Err(ExecutionError::Exception("error".into())));
                }
            )*
        }
    }

    callback_argn_tests![
        1: (a : 1),
    ]
}

#[test]
fn test_callback_varargs() {
    let c = Context::new().unwrap();

    // No return.
    c.add_callback("cb", |args: Arguments| {
        let args = args.into_vec();
        assert_eq!(
            args,
            vec![
                JsValue::String("hello".into()),
                JsValue::Bool(true),
                JsValue::from(100),
            ]
        );
    })
    .unwrap();
    assert_eq!(
        c.eval_as::<bool>("cb('hello', true, 100) === undefined")
            .unwrap(),
        true
    );

    // With return.
    c.add_callback("cb2", |args: Arguments| -> u32 {
        let args = args.into_vec();
        assert_eq!(
            args,
            vec![JsValue::from(1), JsValue::from(10), JsValue::from(100),]
        );
        111
    })
    .unwrap();
    c.eval(
        r#"
        var x = cb2(1, 10, 100);
        if (x !== 111) {
        throw new Error('Expected 111, got ' + x);
        }
    "#,
    )
    .unwrap();
}

#[test]
fn test_callback_invalid_argcount() {
    let c = Context::new().unwrap();

    c.add_callback("cb", |a: i32, b: i32| a + b).unwrap();

    assert_eq!(
        c.eval(" cb(5) "),
        Err(ExecutionError::Exception(
            "Invalid argument count: Expected 2, got 1".into()
        )),
    );
}

#[test]
fn memory_limit_exceeded() {
    let c = Context::builder().memory_limit(100_000).build().unwrap();
    assert_eq!(
        c.eval("  'abc'.repeat(200_000) "),
        Err(ExecutionError::OutOfMemory),
    );
}

#[test]
fn context_reset() {
    let c = Context::new().unwrap();
    c.eval(" var x = 123; ").unwrap();
    c.add_callback("myCallback", || true).unwrap();

    let c2 = c.reset().unwrap();

    // Check it still works.
    assert_eq!(
        c2.eval_as::<String>(" 'abc'.repeat(2) ").unwrap(),
        "abcabc".to_string(),
    );

    // Check old state is gone.
    let err_msg = c2.eval(" x ").unwrap_err().to_string();
    assert!(err_msg.contains("ReferenceError"));

    // Check callback is gone.
    let err_msg = c2.eval(" myCallback() ").unwrap_err().to_string();
    assert!(err_msg.contains("ReferenceError"));
}

#[inline(never)]
fn build_context() -> Context {
    let ctx = Context::new().unwrap();
    let name = "cb".to_string();
    ctx.add_callback(&name, |a: String| a.repeat(2)).unwrap();

    let code = " function f(value) { return cb(value); } ".to_string();
    ctx.eval(&code).unwrap();

    ctx
}

#[test]
fn moved_context() {
    let c = build_context();
    let v = c.call_function("f", vec!["test"]).unwrap();
    assert_eq!(v, "testtest".into());

    let v = c.eval(" f('la') ").unwrap();
    assert_eq!(v, "lala".into());
}

#[cfg(feature = "chrono")]
#[test]
fn chrono_serialize() {
    let c = build_context();

    c.eval(
        "
        function dateToTimestamp(date) {
            return date.getTime();
        }
    ",
    )
    .unwrap();

    let now = chrono::Utc::now();
    let now_millis = now.timestamp_millis();

    let timestamp = c
        .call_function("dateToTimestamp", vec![JsValue::Date(now)])
        .unwrap();

    assert_eq!(timestamp, JsValue::Float(now_millis as f64));
}

#[cfg(feature = "chrono")]
#[test]
fn chrono_deserialize() {
    use chrono::offset::TimeZone;

    let c = build_context();

    let value = c.eval(" new Date(1234567555) ").unwrap();
    let datetime = chrono::Utc.timestamp_millis_opt(1234567555).unwrap();

    assert_eq!(value, JsValue::Date(datetime));
}

#[cfg(feature = "chrono")]
#[test]
fn chrono_roundtrip() {
    let c = build_context();

    c.eval(" function identity(x) { return x; } ").unwrap();
    let d = chrono::Utc::now();
    let td = JsValue::Date(d);
    let td2 = c.call_function("identity", vec![td]).unwrap();
    let d2 = if let JsValue::Date(x) = td2 {
        x
    } else {
        panic!("expected date")
    };

    assert_eq!(d.timestamp_millis(), d2.timestamp_millis());
}

#[cfg(feature = "bigint")]
#[test]
fn test_bigint_deserialize_i64() {
    for i in vec![0, std::i64::MAX, std::i64::MIN] {
        let c = Context::new().unwrap();
        let value = c.eval(&format!("{}n", i)).unwrap();
        assert_eq!(value, JsValue::BigInt(i.into()));
    }
}

#[cfg(feature = "bigint")]
#[test]
fn test_bigint_deserialize_bigint() {
    for i in vec![
        std::i64::MAX as i128 + 1,
        std::i64::MIN as i128 - 1,
        std::i128::MAX,
        std::i128::MIN,
    ] {
        let c = Context::new().unwrap();
        let value = c.eval(&format!("{}n", i)).unwrap();
        let expected = num_bigint::BigInt::from(i);
        assert_eq!(value, JsValue::BigInt(expected.into()));
    }
}

#[cfg(feature = "bigint")]
#[test]
fn test_bigint_serialize_i64() {
    for i in vec![0, std::i64::MAX, std::i64::MIN] {
        let c = Context::new().unwrap();
        c.eval(&format!(" function isEqual(x) {{ return x === {}n }} ", i))
            .unwrap();
        assert_eq!(
            c.call_function("isEqual", vec![JsValue::BigInt(i.into())])
                .unwrap(),
            JsValue::Bool(true)
        );
    }
}

#[cfg(feature = "bigint")]
#[test]
fn test_bigint_serialize_bigint() {
    for i in vec![
        std::i64::MAX as i128 + 1,
        std::i64::MIN as i128 - 1,
        std::i128::MAX,
        std::i128::MIN,
    ] {
        let c = Context::new().unwrap();
        c.eval(&format!(" function isEqual(x) {{ return x === {}n }} ", i))
            .unwrap();
        let value = JsValue::BigInt(num_bigint::BigInt::from(i).into());
        assert_eq!(
            c.call_function("isEqual", vec![value]).unwrap(),
            JsValue::Bool(true)
        );
    }
}

#[cfg(feature = "patch-dateparser")]
mod dateparser {
    use super::*;

    use rstest::rstest;

    #[test]
    fn test_console() {
        use console::Level;
        use std::sync::{Arc, Mutex};

        let messages = Arc::new(Mutex::new(Vec::<(Level, Vec<JsValue>)>::new()));

        let m = messages.clone();
        let c = Context::builder()
            .console(move |level: Level, args: Vec<JsValue>| {
                m.lock().unwrap().push((level, args));
            })
            .build()
            .unwrap();

        c.eval(
            r#"
        console.log("hi");
        console.error(false);
    "#,
        )
        .unwrap();

        let m = messages.lock().unwrap();

        assert_eq!(
            *m,
            vec![
                (Level::Log, vec![JsValue::from("hi")]),
                (Level::Error, vec![JsValue::from(false)]),
            ]
        );
    }

    #[test]
    fn test_global_setter() {
        let ctx = Context::new().unwrap();
        ctx.set_global("a", "a").unwrap();
        ctx.eval("a + 1").unwrap();
    }

    // Test suite was taken from V8
    // Source: https://github.com/v8/v8/blob/9433ad119aadfe10d60935029195c31f25ab8624/test/mjsunit/date-parse.js

    #[rstest]
    // testCasesES5Misc
    #[case("2000-01-01T08:00:00.000Z", 946713600000)]
    #[case("2000-01-01T08:00:00Z", 946713600000)]
    #[case("2000-01-01T08:00Z", 946713600000)]
    #[case("2000-01T08:00:00.000Z", 946713600000)]
    #[case("2000T08:00:00.000Z", 946713600000)]
    #[case("2000T08:00Z", 946713600000)]
    #[case("2000-01T00:00:00.000-08:00", 946713600000)]
    #[case("2000-01T08:00:00.001Z", 946713600001)]
    #[case("2000-01T08:00:00.099Z", 946713600099)]
    #[case("2000-01T08:00:00.999Z", 946713600999)]
    #[case("2000-01T00:00:00.001-08:00", 946713600001)]
    #[case("2000-01-01T24:00Z", 946771200000)]
    #[case("2000-01-01T24:00:00Z", 946771200000)]
    #[case("2000-01-01T24:00:00.000Z", 946771200000)]
    fn test_date_iso(#[case] input: &str, #[case] expect: i64) {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(&format!(r#"new Date("{input}").getTime()"#))
            .unwrap();

        let n: f64 = res.try_into().unwrap();
        assert_eq!(n, expect as f64);
    }

    #[rstest]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT", 946713600000)]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT+0", 946713600000)]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT+00", 946713600000)]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT+000", 946713600000)]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT+0000", 946713600000)]
    #[case("Sat, 01-Jan-2000 08:00:00 GMT+00:00", 946713600000)]
    #[case("Sat, 01 Jan 2000 08:00:00 GMT", 946713600000)]
    #[case("Saturday, 01-Jan-00 08:00:00 GMT", 946713600000)]
    #[case("01 Jan 00 08:00 -0000", 946713600000)]
    #[case("01 Jan 00 08:00 +0000", 946713600000)]
    fn test_date_gmt(#[case] input: &str, #[case] expect: i64) {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(&format!(r#"new Date("{input}").getTime()"#))
            .unwrap();

        let n: f64 = res.try_into().unwrap();
        assert_eq!(n, expect as f64);
    }

    #[rstest]
    // EST (-5:00)
    #[case("Sat, 01-Jan-2000 03:00:00 UTC-0500", 946713600000)]
    #[case("Sat, 01-Jan-2000 03:00:00 UTC-05:00", 946713600000)]
    #[case("Sat, 01-Jan-2000 03:00:00 EST", 946713600000)]
    #[case("Sat, 01 Jan 2000 03:00:00 EST", 946713600000)]
    #[case("Saturday, 01-Jan-00 03:00:00 EST", 946713600000)]
    #[case("01 Jan 00 03:00 -0500", 946713600000)]
    // EDT (-4:00)
    #[case("Sat, 01-Jan-2000 04:00:00 EDT", 946713600000)]
    #[case("Sat, 01 Jan 2000 04:00:00 EDT", 946713600000)]
    #[case("Saturday, 01-Jan-00 04:00:00 EDT", 946713600000)]
    #[case("01 Jan 00 04:00 -0400", 946713600000)]
    // CST (-6:00)
    #[case("Sat, 01-Jan-2000 02:00:00 CST", 946713600000)]
    #[case("Sat, 01 Jan 2000 02:00:00 CST", 946713600000)]
    #[case("Saturday, 01-Jan-00 02:00:00 CST", 946713600000)]
    #[case("01 Jan 00 02:00 -0600", 946713600000)]
    // CDT (-5:00)
    #[case("Sat, 01-Jan-2000 03:00:00 CDT", 946713600000)]
    #[case("Sat, 01 Jan 2000 03:00:00 CDT", 946713600000)]
    #[case("Saturday, 01-Jan-00 03:00:00 CDT", 946713600000)]
    #[case("01 Jan 00 03:00 -0500", 946713600000)]
    // MST (-7:00)
    #[case("Sat, 01-Jan-2000 01:00:00 MST", 946713600000)]
    #[case("Sat, 01 Jan 2000 01:00:00 MST", 946713600000)]
    #[case("Saturday, 01-Jan-00 01:00:00 MST", 946713600000)]
    #[case("01 Jan 00 01:00 -0700", 946713600000)]
    // MDT (-6:00)
    #[case("Sat, 01-Jan-2000 02:00:00 MDT", 946713600000)]
    #[case("Sat, 01 Jan 2000 02:00:00 MDT", 946713600000)]
    #[case("Saturday, 01-Jan-00 02:00:00 MDT", 946713600000)]
    #[case("01 Jan 00 02:00 -0600", 946713600000)]
    // PST (-8:00)
    #[case("Sat, 01-Jan-2000 00:00:00 PST", 946713600000)]
    #[case("Sat, 01 Jan 2000 00:00:00 PST", 946713600000)]
    #[case("Saturday, 01-Jan-00 00:00:00 PST", 946713600000)]
    #[case("01 Jan 00 00:00 -0800", 946713600000)]
    #[case("Sat, 01-Jan-2000 PST", 946713600000)]
    // PDT (-7:00)
    #[case("Sat, 01-Jan-2000 01:00:00 PDT", 946713600000)]
    #[case("Sat, 01 Jan 2000 01:00:00 PDT", 946713600000)]
    #[case("Saturday, 01-Jan-00 01:00:00 PDT", 946713600000)]
    #[case("01 Jan 00 01:00 -0700", 946713600000)]
    fn test_date_tz(#[case] input: &str, #[case] expect: i64) {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(&format!(r#"new Date("{input}").getTime()"#))
            .unwrap();

        let n: f64 = res.try_into().unwrap();
        assert_eq!(n, expect as f64);
    }

    #[rstest]
    // Special handling for years in the [0, 100) range.
    #[case("Sat, 01 Jan 0 08:00:00 UT", 946713600000)] // year 2000
    #[case("Sat, 01 Jan 49 08:00:00 UT", 2493100800000)] // year 2049
    #[case("Sat, 01 Jan 50 08:00:00 UT", -631123200000)] // year 1950
    #[case("Sat, 01 Jan 99 08:00:00 UT", 915177600000)] // year 1999
    #[case("Sat, 01 Jan 100 08:00:00 UT", -59011430400000)] // year 100
    // Test PM after time.
    #[case("Sat, 01-Jan-2000 08:00 PM UT", 946756800000)]
    #[case("Sat, 01 Jan 2000 08:00 PM UT", 946756800000)]
    #[case("Jan 01 2000 08:00 PM UT", 946756800000)]
    #[case("Jan 01 08:00 PM UT 2000", 946756800000)]
    #[case("Saturday, 01-Jan-00 08:00 PM UT", 946756800000)]
    #[case("01 Jan 00 08:00 PM +0000", 946756800000)]
    fn test_date_special(#[case] input: &str, #[case] expect: i64) {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(&format!(r#"new Date("{input}").getTime()"#))
            .unwrap();

        let n: f64 = res.try_into().unwrap();
        assert_eq!(n, expect as f64);
    }

    #[rstest]
    #[case("2000-01-01TZ")]
    #[case("2000-01-01T60Z")]
    #[case("2000-01-01T60:60Z")]
    #[case("2000-01-0108:00Z")]
    #[case("2000-01-01T08Z")]
    #[case("2000-01-01T24:01")]
    #[case("2000-01-01T24:00:01")]
    #[case("2000-01-01T24:00:00.001")]
    #[case("2000-01-01T24:00:00.999Z")]
    #[case("May 25 2008 1:30 (PM)) UTC")]
    #[case("May 25 2008 1:30( )AM (PM)")]
    #[case("a1")]
    #[case("nasfdjklsfjoaifg1")]
    #[case("x_2")]
    #[case("May 25 2008 AAA (GMT)")]
    fn test_date_invalid(#[case] input: &str) {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(&format!(r#"new Date("{input}").getTime()"#))
            .unwrap();

        let n: f64 = res.try_into().unwrap();
        assert!(n.is_nan(), "got: {n}");
    }

    #[test]
    fn test_date_ut() {
        let test_cases_ut = vec![
            "Sat, 01-Jan-2000 08:00:00 UT",
            "Sat, 01 Jan 2000 08:00:00 UT",
            "Jan 01 2000 08:00:00 UT",
            "Jan 01 08:00:00 UT 2000",
            "Saturday, 01-Jan-00 08:00:00 UT",
            "01 Jan 00 08:00 +0000",
            // Ignore weekdays.
            "Mon, 01 Jan 2000 08:00:00 UT",
            "Tue, 01 Jan 2000 08:00:00 UT",
            // Ignore prefix that is not part of a date.
            "[Saturday] Jan 01 08:00:00 UT 2000",
            "Ignore all of this stuff because it is annoying 01 Jan 2000 08:00:00 UT",
            "[Saturday] Jan 01 2000 08:00:00 UT",
            "All of this stuff is really annnoying, so it will be ignored Jan 01 2000 08:00:00 UT",
            // If the three first letters of the month is a
            // month name we are happy - ignore the rest.
            "Sat, 01-Janisamonth-2000 08:00:00 UT",
            "Sat, 01 Janisamonth 2000 08:00:00 UT",
            "Janisamonth 01 2000 08:00:00 UT",
            "Janisamonth 01 08:00:00 UT 2000",
            "Saturday, 01-Janisamonth-00 08:00:00 UT",
            "01 Janisamonth 00 08:00 +0000",
            // Allow missing space between month and day.
            "Janisamonthandtherestisignored01 2000 08:00:00 UT",
            "Jan01 2000 08:00:00 UT",
            // Allow year/month/day format.
            "Sat, 2000/01/01 08:00:00 UT",
            // Allow month/day/year format.
            "Sat, 01/01/2000 08:00:00 UT",
            // Allow month/day year format.
            "Sat, 01/01 2000 08:00:00 UT",
            // Allow comma instead of space after day, month and year.
            "Sat, 01,Jan,2000,08:00:00 UT",
            // Seconds are optional.
            "Sat, 01-Jan-2000 08:00 UT",
            "Sat, 01 Jan 2000 08:00 UT",
            "Jan 01 2000 08:00 UT",
            "Jan 01 08:00 UT 2000",
            "Saturday, 01-Jan-00 08:00 UT",
            "01 Jan 00 08:00 +0000",
            // Allow AM/PM after the time.
            "Sat, 01-Jan-2000 08:00 AM UT",
            "Sat, 01 Jan 2000 08:00 AM UT",
            "Jan 01 2000 08:00 AM UT",
            "Jan 01 08:00 AM UT 2000",
            "Saturday, 01-Jan-00 08:00 AM UT",
            "01 Jan 00 08:00 AM +0000",
            // White space and stuff in parenthesis is
            // apparently allowed in most places where white
            // space is allowed.
            "   Sat,   01-Jan-2000   08:00:00   UT  ",
            "  Sat,   01   Jan   2000   08:00:00   UT  ",
            "  Saturday,   01-Jan-00   08:00:00   UT  ",
            "  01    Jan   00    08:00   +0000   ",
            " ()(Sat, 01-Jan-2000)  Sat,   01-Jan-2000   08:00:00   UT  ",
            "  Sat()(Sat, 01-Jan-2000)01   Jan   2000   08:00:00   UT  ",
            "  Sat,(02)01   Jan   2000   08:00:00   UT  ",
            "  Sat,  01(02)Jan   2000   08:00:00   UT  ",
            "  Sat,  01  Jan  2000 (2001)08:00:00   UT  ",
            "  Sat,  01  Jan  2000 (01)08:00:00   UT  ",
            "  Sat,  01  Jan  2000 (01:00:00)08:00:00   UT  ",
            "  Sat,  01  Jan  2000  08:00:00 (CDT)UT  ",
            "  Sat,  01  Jan  2000  08:00:00  UT((((CDT))))",
            "  Saturday,   01-Jan-00 ()(((asfd)))(Sat, 01-Jan-2000)08:00:00   UT  ",
            "  01    Jan   00    08:00 ()(((asdf)))(Sat, 01-Jan-2000)+0000   ",
            "  01    Jan   00    08:00   +0000()((asfd)(Sat, 01-Jan-2000)) ",
        ];

        let mut passed = 0;
        let mut failed = 0;

        for case in test_cases_ut {
            let ctx = Context::new().unwrap();
            let res = ctx
                .eval(&format!(r#"new Date("{case}").getTime()"#))
                .unwrap();
            let n: f64 = res.try_into().unwrap();

            if n == 946713600000.0 {
                passed += 1;
            } else {
                println!("FAIL: `{case}`  -  {n}");
                failed += 1;
            }
        }

        println!("{}/{} Passed", passed, passed + failed);
        assert_eq!(failed, 0);
    }

    #[test]
    // Test if the JS interpreter can parse its own date format
    // (Dates from 1970 to ~2070 with 150h steps.)
    fn test_date_selfparse() {
        let ctx = Context::new().unwrap();
        let res = ctx
            .eval(
                r#"
        test = () => {
            for (var i = 0; i < 24 * 365 * 100; i += 150) {
                var ms = i * (3600 * 1000);
                var s = (new Date(ms)).toString();
                if(ms != Date.parse(s)) return false;
            }
            return true;
        }
        test();
        "#,
            )
            .unwrap();
        let res: bool = res.try_into().unwrap();
        assert!(res);
    }
}
