(function() {var type_impls = {
"oak_sev_guest":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortReader%3Cu16%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#124-133\">source</a><a href=\"#impl-PortReader%3Cu16%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortReader.html\" title=\"trait oak_sev_guest::io::PortReader\">PortReader</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_read\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#130-132\">source</a><a href=\"#method.try_read\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\" class=\"fn\">try_read</a>(&amp;mut self) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to read from the port. <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\">Read more</a></div></details></div></details>","PortReader<u16>","oak_sev_guest::io::StaticGhcbIoPort"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortWriter%3Cu8%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#146-155\">source</a><a href=\"#impl-PortWriter%3Cu8%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortWriter.html\" title=\"trait oak_sev_guest::io::PortWriter\">PortWriter</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_write\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#152-154\">source</a><a href=\"#method.try_write\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\" class=\"fn\">try_write</a>(&amp;mut self, value: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to write a value to the port. <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\">Read more</a></div></details></div></details>","PortWriter<u8>","oak_sev_guest::io::StaticGhcbIoPort"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortReader%3Cu8%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#113-122\">source</a><a href=\"#impl-PortReader%3Cu8%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortReader.html\" title=\"trait oak_sev_guest::io::PortReader\">PortReader</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_read\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#119-121\">source</a><a href=\"#method.try_read\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\" class=\"fn\">try_read</a>(&amp;mut self) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to read from the port. <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\">Read more</a></div></details></div></details>","PortReader<u8>","oak_sev_guest::io::StaticGhcbIoPort"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortReader%3Cu32%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#135-144\">source</a><a href=\"#impl-PortReader%3Cu32%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortReader.html\" title=\"trait oak_sev_guest::io::PortReader\">PortReader</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_read\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#141-143\">source</a><a href=\"#method.try_read\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\" class=\"fn\">try_read</a>(&amp;mut self) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to read from the port. <a href=\"oak_sev_guest/io/trait.PortReader.html#tymethod.try_read\">Read more</a></div></details></div></details>","PortReader<u32>","oak_sev_guest::io::StaticGhcbIoPort"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortWriter%3Cu32%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#168-177\">source</a><a href=\"#impl-PortWriter%3Cu32%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortWriter.html\" title=\"trait oak_sev_guest::io::PortWriter\">PortWriter</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_write\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#174-176\">source</a><a href=\"#method.try_write\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\" class=\"fn\">try_write</a>(&amp;mut self, value: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to write a value to the port. <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\">Read more</a></div></details></div></details>","PortWriter<u32>","oak_sev_guest::io::StaticGhcbIoPort"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PortWriter%3Cu16%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#157-166\">source</a><a href=\"#impl-PortWriter%3Cu16%3E-for-GhcbIoPort%3C'a,+R,+P,+G%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'a, R, P, G&gt; <a class=\"trait\" href=\"oak_sev_guest/io/trait.PortWriter.html\" title=\"trait oak_sev_guest::io::PortWriter\">PortWriter</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>&gt; for <a class=\"struct\" href=\"oak_sev_guest/io/struct.GhcbIoPort.html\" title=\"struct oak_sev_guest::io::GhcbIoPort\">GhcbIoPort</a>&lt;'a, R, P, G&gt;<div class=\"where\">where\n    R: RawMutex + 'a,\n    P: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.GhcbProtocol.html\" title=\"struct oak_sev_guest::ghcb::GhcbProtocol\">GhcbProtocol</a>&lt;'a, G&gt;&gt; + 'a + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,\n    G: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsMut.html\" title=\"trait core::convert::AsMut\">AsMut</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/convert/trait.AsRef.html\" title=\"trait core::convert::AsRef\">AsRef</a>&lt;<a class=\"struct\" href=\"oak_sev_guest/ghcb/struct.Ghcb.html\" title=\"struct oak_sev_guest::ghcb::Ghcb\">Ghcb</a>&gt; + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + 'a,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.try_write\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/oak_sev_guest/io.rs.html#163-165\">source</a><a href=\"#method.try_write\" class=\"anchor\">§</a><h4 class=\"code-header\">unsafe fn <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\" class=\"fn\">try_write</a>(&amp;mut self, value: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, &amp;'static <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.str.html\">str</a>&gt;</h4></section></summary><div class='docblock'>Tries to write a value to the port. <a href=\"oak_sev_guest/io/trait.PortWriter.html#tymethod.try_write\">Read more</a></div></details></div></details>","PortWriter<u16>","oak_sev_guest::io::StaticGhcbIoPort"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()