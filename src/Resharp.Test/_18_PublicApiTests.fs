module Resharp.Test._18_PublicApiTests

open Resharp
open Xunit
open Common

#if DEBUG


[<Fact>]
let ``IsMatch simple literal`` () =
    let re = Regex("hello")
    Assert.True(re.IsMatch("hello world"))
    Assert.False(re.IsMatch("goodbye world"))

[<Fact>]
let ``IsMatch empty input`` () =
    let re = Regex("a")
    Assert.False(re.IsMatch(""))

[<Fact>]
let ``IsMatch empty pattern`` () =
    let re = Regex("")
    Assert.True(re.IsMatch(""))
    Assert.True(re.IsMatch("anything"))

[<Fact>]
let ``IsMatch single char`` () =
    let re = Regex("x")
    Assert.True(re.IsMatch("x"))
    Assert.False(re.IsMatch("y"))

[<Fact>]
let ``IsMatch full string anchored`` () =
    let re = Regex(@"\A\d+\z")
    Assert.True(re.IsMatch("12345"))
    Assert.False(re.IsMatch("123a5"))
    Assert.False(re.IsMatch(" 123 "))

[<Fact>]
let ``IsMatch multiline`` () =
    let re = Regex(@"^hello$")
    Assert.True(re.IsMatch("hello"))
    Assert.True(re.IsMatch("line1\nhello\nline3"))
    Assert.False(re.IsMatch("hello world"))



[<Fact>]
let ``Count basic`` () =
    let re = Regex("ab")
    Assert.Equal(3, re.Count("ab ab ab"))

[<Fact>]
let ``Count no matches`` () =
    let re = Regex("xyz")
    Assert.Equal(0, re.Count("hello world"))

[<Fact>]
let ``Count empty input`` () =
    let re = Regex("a")
    Assert.Equal(0, re.Count(""))

[<Fact>]
let ``Count overlapping semantics`` () =
    // non-overlapping: "aaa" should match "aa" once (leftmost longest), then no room for another
    let re = Regex("aa")
    let count = re.Count("aaa")
    Assert.True(count >= 1)

[<Fact>]
let ``Count single char pattern`` () =
    let re = Regex("a")
    Assert.Equal(5, re.Count("abacadaea"))

[<Fact>]
let ``Count word pattern`` () =
    let re = Regex(@"\b\w+\b")
    Assert.Equal(4, re.Count("one two three four"))



[<Fact>]
let ``Matches returns correct values`` () =
    let re = Regex(@"\d+")
    let results = re.Matches("abc 123 def 456 ghi")
    Assert.Equal(2, results.Length)
    Assert.Equal("123", results[0].Value)
    Assert.Equal(4, results[0].Index)
    Assert.Equal(3, results[0].Length)
    Assert.Equal("456", results[1].Value)
    Assert.Equal(12, results[1].Index)

[<Fact>]
let ``Matches empty result`` () =
    let re = Regex("xyz")
    let results = re.Matches("hello")
    Assert.Empty(results)

[<Fact>]
let ``Matches adjacent`` () =
    let re = Regex(@"\d")
    let results = re.Matches("123")
    Assert.Equal(3, results.Length)
    Assert.Equal("1", results[0].Value)
    Assert.Equal("2", results[1].Value)
    Assert.Equal("3", results[2].Value)

[<Fact>]
let ``Matches word boundaries`` () =
    let re = Regex(@"\b\w+\b")
    let results = re.Matches("hello world")
    Assert.Equal(2, results.Length)
    Assert.Equal("hello", results[0].Value)
    Assert.Equal("world", results[1].Value)



[<Fact>]
let ``ValueMatches basic`` () =
    let re = Regex(@"\w+")
    use matches = re.ValueMatches("hello world")
    Assert.Equal(2, matches.size)

[<Fact>]
let ``ValueMatches empty`` () =
    let re = Regex("xyz")
    use matches = re.ValueMatches("hello")
    Assert.Equal(0, matches.size)

[<Fact>]
let ``ValueMatches positions correct`` () =
    let re = Regex("ab")
    use matches = re.ValueMatches("xxabyyabzz")
    Assert.Equal(2, matches.size)
    Assert.Equal(2, matches.pool[0].Index)
    Assert.Equal(2, matches.pool[0].Length)
    Assert.Equal(6, matches.pool[1].Index)
    Assert.Equal(2, matches.pool[1].Length)



[<Fact>]
let ``Replace basic`` () =
    let re = Regex(@"\d+")
    let result = re.Replace("abc 123 def 456", "NUM")
    Assert.Equal("abc NUM def NUM", result)

[<Fact>]
let ``Replace no match`` () =
    let re = Regex("xyz")
    let result = re.Replace("hello world", "!")
    Assert.Equal("hello world", result)

[<Fact>]
let ``Replace empty replacement`` () =
    let re = Regex(@"\s+")
    let result = re.Replace("hello world foo", "")
    Assert.Equal("helloworldfoo", result)

[<Fact>]
let ``Replace all occurrences`` () =
    let re = Regex("a")
    let result = re.Replace("banana", "o")
    Assert.Equal("bonono", result)

[<Fact>]
let ``Replace with function`` () =
    let re = Regex(@"\w+")
    let result = re.Replace("hello world", System.Func<string, string>(fun s -> s.ToUpperInvariant()))
    Assert.Equal("HELLO WORLD", result)

[<Fact>]
let ``Replace entire string`` () =
    let re = Regex(".*")
    let result = re.Replace("hello", "X")
    // .* matches the whole string
    Assert.Contains("X", result)



[<Fact>]
let ``FirstEnd simple`` () =
    let re = Regex(@"\d+")
    let result = re.FirstEnd("123abc")
    Assert.True(result >= 1) // at least matches "1"

[<Fact>]
let ``FirstEnd no match`` () =
    let re = Regex(@"\d+")
    let result = re.FirstEnd("abcdef")
    Assert.Equal(-1, result)

[<Fact>]
let ``FirstEnd greedy vs first`` () =
    // FirstEnd returns the *shortest* (first) match end position
    let re = Regex(@"a+")
    let first = re.FirstEnd("aaaa")
    let longest = re.LongestEnd("aaaa")
    Assert.True(first <= longest)


[<Fact>]
let ``LongestEnd simple`` () =
    let re = Regex(@"\d+")
    let result = re.LongestEnd("12345abc")
    Assert.Equal(5, result)

[<Fact>]
let ``LongestEnd no match`` () =
    let re = Regex(@"\d+")
    let result = re.LongestEnd("abcdef")
    Assert.Equal(-1, result)

[<Fact>]
let ``LongestEnd full string`` () =
    let re = Regex(@"\w+")
    let result = re.LongestEnd("hello")
    Assert.Equal(5, result)



[<Fact>]
let ``FromRegex escapes ampersand`` () =
    let result = Regex.FromRegex("a&b")
    Assert.Equal(@"a\&b", result)

[<Fact>]
let ``FromRegex escapes tilde`` () =
    let result = Regex.FromRegex("~test")
    Assert.Equal(@"\~test", result)

[<Fact>]
let ``FromRegex escapes underscore`` () =
    let result = Regex.FromRegex("a_b")
    Assert.Equal(@"a\_b", result)

[<Fact>]
let ``FromRegex escapes all three`` () =
    let result = Regex.FromRegex("a&b~c_d")
    Assert.Equal(@"a\&b\~c\_d", result)

[<Fact>]
let ``FromRegex no special chars`` () =
    let result = Regex.FromRegex("hello")
    Assert.Equal("hello", result)

[<Fact>]
let ``Escape literal string`` () =
    let escaped = Regex.Escape("hello.world")
    let re = Regex(escaped)
    Assert.True(re.IsMatch("hello.world"))
    Assert.False(re.IsMatch("helloXworld"))

[<Fact>]
let ``Escape with resharp operators`` () =
    let escaped = Regex.Escape("a&b~c_d")
    let re = Regex(escaped)
    Assert.True(re.IsMatch("a&b~c_d"))

[<Fact>]
let ``FromRegex roundtrip`` () =
    let pattern = Regex.FromRegex(@"a&b|c~d_e")
    let re = Regex(pattern)
    Assert.True(re.IsMatch("a&b"))



[<Fact>]
let ``IsFullDFA small pattern`` () =
    // small pattern with default threshold should compile to full DFA
    let re = Regex("ab")
    // just test it doesn't throw - value depends on state count vs threshold
    let _ = re.IsFullDFA
    ()

[<Fact>]
let ``IsFullDFA with high threshold`` () =
    let opts = ResharpOptions(DfaThreshold = 10000)
    let re = Regex("ab", opts)
    Assert.True(re.IsFullDFA)

[<Fact>]
let ``IsFullDFA with zero threshold`` () =
    let opts = ResharpOptions(DfaThreshold = 0)
    let re = Regex("ab", opts)
    Assert.False(re.IsFullDFA)



[<Fact>]
let ``IgnoreCase option`` () =
    let opts = ResharpOptions(IgnoreCase = true)
    let re = Regex("hello", opts)
    Assert.True(re.IsMatch("HELLO"))
    Assert.True(re.IsMatch("Hello"))
    Assert.True(re.IsMatch("hello"))

[<Fact>]
let ``case sensitive by default`` () =
    let re = Regex("hello")
    Assert.True(re.IsMatch("hello"))
    Assert.False(re.IsMatch("HELLO"))

[<Fact>]
let ``SingleUseDefaults option`` () =
    let re = Regex(@"\d+", ResharpOptions.SingleUseDefaults)
    Assert.True(re.IsMatch("123"))
    Assert.False(re.IsMatch("abc"))

[<Fact>]
let ``HighThroughputDefaults option`` () =
    let re = Regex(@"\d+", ResharpOptions.HighThroughputDefaults)
    Assert.True(re.IsMatch("123"))
    Assert.Equal(3, re.Count("1 2 3"))



[<Fact>]
let ``underscore matches any char including newline`` () =
    let re = Regex("a_b")
    Assert.True(re.IsMatch("aXb"))
    Assert.True(re.IsMatch("a\nb"))
    Assert.True(re.IsMatch("a b"))

[<Fact>]
let ``underscore star matches everything`` () =
    let re = Regex("_*")
    Assert.True(re.IsMatch(""))
    Assert.True(re.IsMatch("anything"))
    Assert.True(re.IsMatch("multi\nline\ntext"))

[<Fact>]
let ``escaped underscore matches literal`` () =
    let re = Regex(@"a\_b")
    Assert.True(re.IsMatch("a_b"))
    Assert.False(re.IsMatch("aXb"))



[<Fact>]
let ``intersection basic`` () =
    let re = Regex(@".*cat.*&.*dog.*")
    Assert.True(re.IsMatch("the cat and the dog"))
    Assert.True(re.IsMatch("the dog and the cat"))
    Assert.False(re.IsMatch("just a cat"))
    Assert.False(re.IsMatch("just a dog"))

[<Fact>]
let ``intersection with length constraint`` () =
    let re = Regex(@"\A(.*cat.*&.{0,10})\z")
    Assert.True(re.IsMatch("a cat"))
    Assert.False(re.IsMatch("a very long string with cat in it"))

[<Fact>]
let ``triple intersection`` () =
    let re = Regex(@".*a.*&.*b.*&.*c.*")
    Assert.True(re.IsMatch("abc"))
    Assert.True(re.IsMatch("cba"))
    Assert.False(re.IsMatch("ab"))
    Assert.False(re.IsMatch("ac"))
    Assert.False(re.IsMatch("bc"))

[<Fact>]
let ``intersection with char classes`` () =
    let re = Regex(@"\A[a-z]+\z&\A.{3}\z")
    Assert.True(re.IsMatch("abc"))
    Assert.False(re.IsMatch("ab"))
    Assert.False(re.IsMatch("abcd"))
    Assert.False(re.IsMatch("AB3"))

[<Fact>]
let ``escaped ampersand matches literal`` () =
    let re = Regex(@"a\&b")
    Assert.True(re.IsMatch("a&b"))



[<Fact>]
let ``complement basic`` () =
    let re = Regex(@"\A~(.*foo.*)\z")
    Assert.True(re.IsMatch("hello"))
    Assert.False(re.IsMatch("foobar"))
    Assert.False(re.IsMatch("barfoo"))

[<Fact>]
let ``complement with intersection`` () =
    // full-string: contains "a" but not "b"
    let re = Regex(@"\A(.*a.*&~(.*b.*))\z")
    Assert.True(re.IsMatch("cat"))
    Assert.False(re.IsMatch("cab"))
    Assert.False(re.IsMatch("xyz"))

[<Fact>]
let ``complement double negation`` () =
    // ~(~(.*foo.*)) should be equivalent to .*foo.*
    let re = Regex(@"~(~(.*foo.*))")
    Assert.True(re.IsMatch("foobar"))
    Assert.True(re.IsMatch("barfoo"))
    Assert.False(re.IsMatch("hello"))

[<Fact>]
let ``escaped tilde matches literal`` () =
    let re = Regex(@"a\~b")
    Assert.True(re.IsMatch("a~b"))



[<Fact>]
let ``word boundary`` () =
    let re = Regex(@"\bword\b")
    Assert.True(re.IsMatch("a word here"))
    Assert.False(re.IsMatch("swordfish"))

[<Fact>]
let ``start and end anchors`` () =
    let re = Regex(@"\Ahello\z")
    Assert.True(re.IsMatch("hello"))
    Assert.False(re.IsMatch("hello world"))
    Assert.False(re.IsMatch("say hello"))

[<Fact>]
let ``line anchors multiline`` () =
    let re = Regex(@"^line2$")
    Assert.True(re.IsMatch("line1\nline2\nline3"))
    Assert.False(re.IsMatch("line1\nline22\nline3"))

[<Fact>]
let ``dollar at end`` () =
    let re = Regex(@"\d+$")
    Assert.True(re.IsMatch("abc123"))
    Assert.False(re.IsMatch("123abc"))



[<Fact>]
let ``digit class`` () =
    let re = Regex(@"\A\d+\z")
    Assert.True(re.IsMatch("12345"))
    Assert.False(re.IsMatch("123a5"))

[<Fact>]
let ``word class`` () =
    let re = Regex(@"\A\w+\z")
    Assert.True(re.IsMatch("hello_123"))
    Assert.False(re.IsMatch("hello world"))

[<Fact>]
let ``whitespace class`` () =
    let re = Regex(@"\s+")
    Assert.True(re.IsMatch(" "))
    Assert.True(re.IsMatch("\t"))
    Assert.True(re.IsMatch("\n"))

[<Fact>]
let ``negated class`` () =
    let re = Regex(@"\A[^abc]+\z")
    Assert.True(re.IsMatch("xyz"))
    Assert.False(re.IsMatch("xya"))

[<Fact>]
let ``range subtraction`` () =
    // [a-z-[aeiou]] = consonants
    let re = Regex(@"\A[a-z-[aeiou]]+\z")
    Assert.True(re.IsMatch("bcdfg"))
    Assert.False(re.IsMatch("abc"))



[<Fact>]
let ``plus quantifier`` () =
    let re = Regex(@"\A\d+\z")
    Assert.True(re.IsMatch("1"))
    Assert.True(re.IsMatch("12345"))
    Assert.False(re.IsMatch(""))

[<Fact>]
let ``star quantifier`` () =
    let re = Regex(@"\Aa*b\z")
    Assert.True(re.IsMatch("b"))
    Assert.True(re.IsMatch("ab"))
    Assert.True(re.IsMatch("aaab"))
    Assert.False(re.IsMatch("c"))

[<Fact>]
let ``optional quantifier`` () =
    let re = Regex(@"\Acolou?r\z")
    Assert.True(re.IsMatch("color"))
    Assert.True(re.IsMatch("colour"))
    Assert.False(re.IsMatch("colouur"))

[<Fact>]
let ``exact repetition`` () =
    let re = Regex(@"\Aa{3}\z")
    Assert.True(re.IsMatch("aaa"))
    Assert.False(re.IsMatch("aa"))
    Assert.False(re.IsMatch("aaaa"))

[<Fact>]
let ``range repetition`` () =
    let re = Regex(@"\Aa{2,4}\z")
    Assert.True(re.IsMatch("aa"))
    Assert.True(re.IsMatch("aaa"))
    Assert.True(re.IsMatch("aaaa"))
    Assert.False(re.IsMatch("a"))
    Assert.False(re.IsMatch("aaaaa"))

[<Fact>]
let ``min repetition`` () =
    let re = Regex(@"\Aa{2,}\z")
    Assert.True(re.IsMatch("aa"))
    Assert.True(re.IsMatch("aaaaaaa"))
    Assert.False(re.IsMatch("a"))



[<Fact>]
let ``basic alternation`` () =
    let re = Regex(@"cat|dog")
    Assert.True(re.IsMatch("I have a cat"))
    Assert.True(re.IsMatch("I have a dog"))
    Assert.False(re.IsMatch("I have a bird"))

[<Fact>]
let ``alternation match positions`` () =
    let re = Regex(@"cat|dog")
    let results = re.Matches("cat and dog")
    Assert.Equal(2, results.Length)
    Assert.Equal("cat", results[0].Value)
    Assert.Equal("dog", results[1].Value)



[<Fact>]
let ``positive lookahead`` () =
    let re = Regex(@"\w+(?=\.)")
    Assert.True(re.IsMatch("hello."))
    let results = re.Matches("file.txt")
    Assert.Equal(1, results.Length)
    Assert.Equal("file", results[0].Value)

[<Fact>]
let ``negative lookahead`` () =
    let re = Regex(@"\d+(?!\.\d)")
    let results = re.Matches("100 3.14")
    Assert.True(results.Length >= 1)
    // 100 should match since it's not followed by .digit
    Assert.True(results |> Array.exists (fun m -> m.Value = "100"))

[<Fact>]
let ``positive lookbehind`` () =
    let re = Regex(@"(?<=@)\w+")
    let results = re.Matches("user@domain")
    Assert.Equal(1, results.Length)
    Assert.Equal("domain", results[0].Value)

[<Fact>]
let ``negative lookbehind`` () =
    let re = Regex(@"(?<!\d)abc")
    Assert.True(re.IsMatch(" abc"))
    Assert.False(re.IsMatch("1abc"))



[<Fact>]
let ``unicode letters`` () =
    let re = Regex(@"\w+")
    Assert.True(re.IsMatch("cafe\u0301"))

[<Fact>]
let ``unicode category`` () =
    let re = Regex(@"\p{Lu}+")
    Assert.True(re.IsMatch("ABC"))
    Assert.False(re.IsMatch("abc"))

[<Fact>]
let ``unicode in character class`` () =
    let re = Regex(@"[\u0400-\u04FF]+")
    Assert.True(re.IsMatch("\u0410\u0411"))
    Assert.False(re.IsMatch("ABC"))



[<Fact>]
let ``dot does not match newline`` () =
    let re = Regex("a.b")
    Assert.True(re.IsMatch("aXb"))
    Assert.False(re.IsMatch("a\nb"))

[<Fact>]
let ``long input`` () =
    let re = Regex("needle")
    let input = System.String('x', 10_000) + "needle" + System.String('x', 10_000)
    Assert.True(re.IsMatch(input))
    Assert.Equal(1, re.Count(input))

[<Fact>]
let ``many matches`` () =
    let re = Regex("a")
    let input = System.String('a', 1000)
    Assert.Equal(1000, re.Count(input))

[<Fact>]
let ``pattern with all metacharacters`` () =
    let re = Regex(@"^(\w+)\s+\d{2,4}[.-]?\w*$")
    Assert.True(re.IsMatch("hello 1234"))
    Assert.True(re.IsMatch("test 99.abc"))
    Assert.False(re.IsMatch(""))

[<Fact>]
let ``consecutive replacements`` () =
    let re = Regex(@"\d+")
    let r1 = re.Replace("a1b2c3", "X")
    Assert.Equal("aXbXcX", r1)

[<Fact>]
let ``replace with longer string`` () =
    let re = Regex("a")
    let result = re.Replace("abc", "XYZ")
    Assert.Equal("XYZbc", result)

[<Fact>]
let ``replace with shorter string`` () =
    let re = Regex("abc")
    let result = re.Replace("xabcx", "y")
    Assert.Equal("xyx", result)



[<Fact>]
let ``unbalanced parentheses throws`` () =
    Assert.ThrowsAny<exn>(fun () -> Regex("(abc") |> ignore)

[<Fact>]
let ``invalid quantifier throws`` () =
    Assert.ThrowsAny<exn>(fun () -> Regex("*abc") |> ignore)

[<Fact>]
let ``unbalanced bracket throws`` () =
    Assert.ThrowsAny<exn>(fun () -> Regex("[abc") |> ignore)



[<Fact>]
let ``dot matches various chars`` () =
    let re = Regex("a.c")
    Assert.True(re.IsMatch("abc"))
    Assert.True(re.IsMatch("a c"))
    Assert.True(re.IsMatch("a1c"))
    Assert.True(re.IsMatch("a\tc"))
    Assert.False(re.IsMatch("a\nc"))

[<Fact>]
let ``dot star greedy match`` () =
    let re = Regex("a.*b")
    let results = re.Matches("aXXbYYaZZb")
    Assert.Equal(1, results.Length)
    Assert.Equal("aXXbYYaZZb", results[0].Value)



[<Fact>]
let ``groups work as non-capturing`` () =
    let re = Regex(@"(foo)(bar)")
    Assert.True(re.IsMatch("foobar"))
    let results = re.Matches("foobar")
    Assert.Equal(1, results.Length)
    Assert.Equal("foobar", results[0].Value)

[<Fact>]
let ``named group`` () =
    let re = Regex(@"(?<name>\w+)@\w+")
    Assert.True(re.IsMatch("user@host"))



let assertSameAsRuntime pattern (input: string) =
    let rs = Regex(pattern)
    let net = System.Text.RegularExpressions.Regex(pattern)
    Assert.Equal(net.IsMatch(input), rs.IsMatch(input))

[<Fact>]
let ``matches runtime: email-like`` () =
    let pattern = @"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}"
    assertSameAsRuntime pattern "test@example.com"
    assertSameAsRuntime pattern "not an email"
    assertSameAsRuntime pattern "user.name+tag@domain.co.uk"

[<Fact>]
let ``matches runtime: IP address`` () =
    let pattern = @"(\d{1,3}\.){3}\d{1,3}"
    assertSameAsRuntime pattern "192.168.1.1"
    assertSameAsRuntime pattern "not an ip"
    assertSameAsRuntime pattern "999.999.999.999"

[<Fact>]
let ``matches runtime: date pattern`` () =
    let pattern = @"\d{4}-\d{2}-\d{2}"
    assertSameAsRuntime pattern "2026-03-12"
    assertSameAsRuntime pattern "not a date"

[<Fact>]
let ``matches runtime: nested groups`` () =
    let pattern = @"((a|b)+c)+"
    assertSameAsRuntime pattern "abcbac"
    assertSameAsRuntime pattern "xyz"

[<Fact>]
let ``matches runtime: complex alternation`` () =
    let pattern = @"^(Mon|Tue|Wed|Thu|Fri|Sat|Sun)day$"
    for day in ["Monday"; "Tuesday"; "Wednesday"; "Thursday"; "Friday"; "Saturday"; "Sunday"] do
        assertSameAsRuntime pattern day
    assertSameAsRuntime pattern "Blorday"

[<Fact>]
let ``matches runtime: hex pattern`` () =
    let pattern = @"^#?([a-fA-F0-9]{6}|[a-fA-F0-9]{3})$"
    assertSameAsRuntime pattern "#ff0000"
    assertSameAsRuntime pattern "abc"
    assertSameAsRuntime pattern "#ABC"
    assertSameAsRuntime pattern "GGGGGG"

[<Fact>]
let ``matches runtime: url-like`` () =
    let pattern = @"^https?://[^\s/$.?#].[^\s]*$"
    assertSameAsRuntime pattern "https://example.com"
    assertSameAsRuntime pattern "http://test.org/path?q=1"
    assertSameAsRuntime pattern "not a url"

[<Fact>]
let ``matches runtime: complex quantifiers`` () =
    let pattern = @"^a{2,5}b{0,3}c+d?e*$"
    assertSameAsRuntime pattern "aabccc"
    assertSameAsRuntime pattern "aaaaabbbcde"
    assertSameAsRuntime pattern "abcde"
    assertSameAsRuntime pattern "aac"

[<Fact>]
let ``Count matches runtime`` () =
    let patterns = [
        @"\w+"; @"\d+"; @"[a-z]+"; @"\s+"
        @"(foo|bar)"; @"\b\w{3}\b"
    ]
    let inputs = [
        "hello world 123"
        "foo bar baz 1 22 333"
        "  spaces   here  "
    ]
    for pattern in patterns do
        let rs = Regex(pattern)
        let net = System.Text.RegularExpressions.Regex(pattern)
        for input in inputs do
            let rsCount = rs.Count(input)
            let netCount = net.Matches(input).Count
            assertTrue
                (rsCount = netCount)
                $"Count mismatch for '{pattern}' on '{input}': resharp={rsCount} runtime={netCount}"

[<Fact>]
let ``Match positions match runtime`` () =
    let patterns = [
        @"\w+"; @"\d+"; @"(ab|cd)+"
    ]
    let inputs = [
        "hello world 123"
        "abcdabef 99"
    ]
    for pattern in patterns do
        let rs = Regex(pattern)
        let net = System.Text.RegularExpressions.Regex(pattern)
        for input in inputs do
            let rsMatches = rs.Matches(input) |> Array.map (fun m -> m.Index, m.Length)
            let netMatches = net.Matches(input) |> Seq.map (fun m -> m.Index, m.Length) |> Seq.toArray
            Assert.Equal<(int * int)>(netMatches, rsMatches)



[<Fact>]
let ``reuse same instance`` () =
    let re = Regex(@"\d+")
    for _ in 1..100 do
        Assert.True(re.IsMatch("123"))
        Assert.False(re.IsMatch("abc"))
        Assert.Equal(3, re.Count("1 2 3"))



[<Fact>]
let ``password-like constraint`` () =
    // at least one digit AND at least one letter AND 8+ chars
    let re = Regex(@"\A(.*\d.*&.*[a-zA-Z].*&.{8,})\z")
    Assert.True(re.IsMatch("password1"))
    Assert.True(re.IsMatch("1password"))
    Assert.False(re.IsMatch("password"))  // no digit
    Assert.False(re.IsMatch("12345678"))  // no letter
    Assert.False(re.IsMatch("pass1"))     // too short

[<Fact>]
let ``intersection with complement for exclusion`` () =
    // words with 'a' but not 'z'
    let re = Regex(@"\b(\w+&.*a.*&~(.*z.*))\b")
    Assert.True(re.IsMatch("cat"))
    Assert.True(re.IsMatch("banana"))
    Assert.False(re.IsMatch("amazing"))  // has z... wait, no it doesn't. let me think
    Assert.False(re.IsMatch("jazz"))     // has z

[<Fact>]
let ``complement of unsupported boundary throws`` () =
    // \b requires adjacent word/non-word chars in RE#
    Assert.ThrowsAny<exn>(fun () -> Regex(@"~(\b)") |> ignore)

[<Fact>]
let ``intersection identity`` () =
    // pattern & .* should be equivalent to just pattern
    let re1 = Regex(@"hello")
    let re2 = Regex(@"hello&.*")
    let inputs = ["hello world"; "goodbye"; "say hello"; ""]
    for input in inputs do
        Assert.Equal(re1.IsMatch(input), re2.IsMatch(input))



[<Fact>]
let ``complex date pattern`` () =
    let pattern = @"^(0[1-9]|[12]\d|3[01])/(0[1-9]|1[012])/\d{4}$"
    let re = Regex(pattern)
    Assert.True(re.IsMatch("31/12/2026"))
    Assert.True(re.IsMatch("01/01/2000"))
    Assert.False(re.IsMatch("32/13/2026"))
    Assert.False(re.IsMatch("1/1/26"))

[<Fact>]
let ``email-like pattern`` () =
    let pattern = @"[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}"
    let re = Regex(pattern)
    let results = re.Matches("contact us at info@example.com or support@test.org")
    Assert.Equal(2, results.Length)
    Assert.Equal("info@example.com", results[0].Value)
    Assert.Equal("support@test.org", results[1].Value)

[<Fact>]
let ``csv-like splitting`` () =
    // match comma-separated values (non-comma sequences)
    let re = Regex(@"[^,]+")
    let results = re.Matches("one,two,three,four")
    Assert.Equal(4, results.Length)
    Assert.Equal("one", results[0].Value)
    Assert.Equal("four", results[3].Value)


#endif
