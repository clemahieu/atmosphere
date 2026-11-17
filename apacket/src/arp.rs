// SPDX-License-Identifier: MIT

//! `Arp`, the ARP packet (RFC 826) for Ethernet hardware addresses and IPv4 protocol addresses: the
//! hardware type 1 and the protocol type 0x0800, each two bytes big-endian, the address lengths 6
//! and 4, a byte each, the opcode, two bytes big-endian, then the sender's hardware and protocol
//! addresses and the target's, 28 bytes in all. The four fixed fields are `Tag`s, so a packet of
//! another hardware or protocol type, or with other address lengths, is refused; the opcode is a
//! `U16Be` and each address `Bytes` of its length. The value, `ArpPacket`, names the opcode and the
//! four addresses through `Mapped`, and holds no fixed field.

use vstd::prelude::*;

use awire::*;

verus! {

/// An ARP packet for Ethernet and IPv4, by its fields' names. Each address borrows the input.
#[derive(Clone, Copy)]
pub struct ArpPacket<'a> {
    pub opcode: u16,
    pub sender_hardware: &'a [u8],
    pub sender_protocol: &'a [u8],
    pub target_hardware: &'a [u8],
    pub target_protocol: &'a [u8],
}

/// An `ArpPacket` as the specification sees it.
pub ghost struct ArpPacketView {
    pub opcode: u16,
    pub sender_hardware: Seq<u8>,
    pub sender_protocol: Seq<u8>,
    pub target_hardware: Seq<u8>,
    pub target_protocol: Seq<u8>,
}

impl<'a> View for ArpPacket<'a> {
    type V = ArpPacketView;

    open spec fn view(&self) -> ArpPacketView {
        ArpPacketView {
            opcode: self.opcode,
            sender_hardware: self.sender_hardware@,
            sender_protocol: self.sender_protocol@,
            target_hardware: self.target_hardware@,
            target_protocol: self.target_protocol@,
        }
    }
}

/// The combinators' value of an ARP packet: the four fixed fields, the opcode and the four
/// addresses, as nested pairs.
pub type ArpFields<'a> = ((), ((), ((), ((), (u16, (&'a [u8], (&'a [u8], (&'a [u8], &'a [u8]))))))));

/// The ARP packet as awire's combinators read it.
pub type ArpWire = Pair<Tag<'static>, Pair<Tag<'static>, Pair<Tag<'static>, Pair<Tag<'static>, Pair<U16Be, Pair<Bytes, Pair<Bytes, Pair<Bytes, Bytes>>>>>>>>;

/// An `ArpPacket` from the nested pairs of its fields, and back. A conversion moves five fields
/// and reads no byte, so it takes no step.
pub struct ArpMapping;

impl<'a> Mapping<ArpFields<'a>> for ArpMapping {
    type T = ArpPacket<'a>;

    open spec fn spec_into(&self, s: <ArpFields<'a> as View>::V) -> ArpPacketView {
        ArpPacketView {
            opcode: s.1.1.1.1.0,
            sender_hardware: s.1.1.1.1.1.0,
            sender_protocol: s.1.1.1.1.1.1.0,
            target_hardware: s.1.1.1.1.1.1.1.0,
            target_protocol: s.1.1.1.1.1.1.1.1,
        }
    }

    open spec fn spec_from(&self, t: ArpPacketView) -> <ArpFields<'a> as View>::V {
        ((), ((), ((), ((), (t.opcode, (t.sender_hardware, (t.sender_protocol, (t.target_hardware, t.target_protocol))))))))
    }

    open spec fn c(&self) -> nat {
        0
    }

    proof fn lemma_from_into(&self, s: <ArpFields<'a> as View>::V) {
        let (a, (b, (c, (d, rest)))) = s;
        assert(a == () && b == () && c == () && d == ());
    }

    proof fn lemma_into_from(&self, t: ArpPacketView) {
    }

    fn map_into(&self, s: ArpFields<'a>, Tracked(steps): Tracked<&mut Steps>) -> (t: ArpPacket<'a>) {
        let (_, (_, (_, (_, (opcode, (sender_hardware, (sender_protocol, (target_hardware, target_protocol)))))))) = s;
        ArpPacket { opcode, sender_hardware, sender_protocol, target_hardware, target_protocol }
    }

    fn map_from(&self, t: &ArpPacket<'a>, Tracked(steps): Tracked<&mut Steps>) -> (s: ArpFields<'a>) {
        ((), ((), ((), ((), (t.opcode, (t.sender_hardware, (t.sender_protocol, (t.target_hardware, t.target_protocol))))))))
    }
}

/// The ARP packet for Ethernet and IPv4. `wf` pins the fixed fields and the address lengths, so
/// every `Arp` a proof holds reads this format; `new` makes one.
pub struct Arp {
    pub wire: Mapped<ArpWire, ArpMapping>,
}

impl Arp {
    /// The ARP combinator for Ethernet and IPv4.
    pub fn new() -> (c: Arp)
        ensures
            c.wf(),
    {
        let hardware: &'static [u8] = &[0x00, 0x01];
        let protocol: &'static [u8] = &[0x08, 0x00];
        let hardware_length: &'static [u8] = &[6];
        let protocol_length: &'static [u8] = &[4];
        assert(hardware@ =~= seq![0x00u8, 0x01u8]);
        assert(protocol@ =~= seq![0x08u8, 0x00u8]);
        assert(hardware_length@ =~= seq![6u8]);
        assert(protocol_length@ =~= seq![4u8]);
        Arp {
            wire: Mapped {
                inner: Pair {
                    first: Tag { bytes: hardware },
                    second: Pair {
                        first: Tag { bytes: protocol },
                        second: Pair {
                            first: Tag { bytes: hardware_length },
                            second: Pair {
                                first: Tag { bytes: protocol_length },
                                second: Pair {
                                    first: U16Be,
                                    second: Pair {
                                        first: Bytes { len: 6 },
                                        second: Pair {
                                            first: Bytes { len: 4 },
                                            second: Pair { first: Bytes { len: 6 }, second: Bytes { len: 4 } },
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
                mapping: ArpMapping,
            },
        }
    }

    /// A packet that starts with Ethernet's hardware type, IPv4's protocol type and the address
    /// lengths 6 and 4 is accepted if it holds the 28 bytes, and its first 28 bytes are consumed.
    pub proof fn lemma_header_accepted(&self, s: Seq<u8>)
        requires
            self.wf(),
            28 <= s.len(),
            s[0] == 0x00 && s[1] == 0x01 && s[2] == 0x08 && s[3] == 0x00 && s[4] == 6 && s[5] == 4,
        ensures
            self.spec_parse(s) is Some,
            (self.spec_parse(s)->0).0 == 28,
    {
        let w = self.wire.inner;
        assert(s.take(2) =~= w.first.bytes@);
        let s1 = s.skip(2);
        assert(s1.take(2) =~= w.second.first.bytes@);
        let s2 = s1.skip(2);
        assert(s2.take(1) =~= w.second.second.first.bytes@);
        let s3 = s2.skip(1);
        assert(s3.take(1) =~= w.second.second.second.first.bytes@);
    }

    /// Every packet this format carries is 28 bytes.
    pub proof fn lemma_serialized_length(&self, v: ArpPacketView)
        requires
            self.wf(),
            self.valid(v),
        ensures
            self.spec_serialize(v).len() == 28,
    {
    }

    /// A packet whose hardware type is not Ethernet's, whose protocol type is not IPv4's, or whose
    /// address lengths are not 6 and 4, is refused, as is one too short to hold them.
    pub proof fn lemma_other_types_refused(&self, s: Seq<u8>)
        requires
            self.wf(),
            s.len() < 6 || s[0] != 0x00 || s[1] != 0x01 || s[2] != 0x08 || s[3] != 0x00 || s[4] != 6 || s[5] != 4,
        ensures
            self.spec_parse(s) is None,
    {
        let w = self.wire.inner;
        if s.len() >= 2 && s.take(2) == w.first.bytes@ {
            assert(s.take(2)[0] == s[0] && s.take(2)[1] == s[1]);
            let s1 = s.skip(2);
            if s1.len() >= 2 && s1.take(2) == w.second.first.bytes@ {
                assert(s1.take(2)[0] == s[2] && s1.take(2)[1] == s[3]);
                let s2 = s1.skip(2);
                if s2.len() >= 1 && s2.take(1) == w.second.second.first.bytes@ {
                    assert(s2.take(1)[0] == s[4]);
                    let s3 = s2.skip(1);
                    if s3.len() >= 1 && s3.take(1) == w.second.second.second.first.bytes@ {
                        assert(s3.take(1)[0] == s[5]);
                    }
                }
            }
        }
    }
}

impl<'a> Combinator<'a> for Arp {
    type V = ArpPacketView;

    type T = ArpPacket<'a>;

    open spec fn wf(&self) -> bool {
        let w = self.wire.inner;
        &&& w.first.bytes@ == seq![0x00u8, 0x01u8]
        &&& w.second.first.bytes@ == seq![0x08u8, 0x00u8]
        &&& w.second.second.first.bytes@ == seq![6u8]
        &&& w.second.second.second.first.bytes@ == seq![4u8]
        &&& w.second.second.second.second.second.first.len == 6
        &&& w.second.second.second.second.second.second.first.len == 4
        &&& w.second.second.second.second.second.second.second.first.len == 6
        &&& w.second.second.second.second.second.second.second.second.len == 4
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(nat, ArpPacketView)> {
        self.wire.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: ArpPacketView) -> Seq<u8> {
        self.wire.spec_serialize(v)
    }

    open spec fn valid(&self, v: ArpPacketView) -> bool {
        self.wire.valid(v)
    }

    open spec fn k(&self) -> nat {
        self.wire.k()
    }

    open spec fn c(&self) -> nat {
        self.wire.c()
    }

    proof fn lemma_parse_serialize(&self, s: Seq<u8>) {
        self.wire.lemma_parse_serialize(s);
    }

    proof fn lemma_serialize_parse(&self, v: ArpPacketView, rest: Seq<u8>) {
        self.wire.lemma_serialize_parse(v, rest);
    }

    fn parse(&self, input: &'a [u8], Tracked(steps): Tracked<&mut Steps>) -> (r: Option<(usize, ArpPacket<'a>)>) {
        self.wire.parse(input, Tracked(steps))
    }

    fn length(&self, v: &ArpPacket<'a>, cap: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        self.wire.length(v, cap, Tracked(steps))
    }

    fn serialize(&self, v: &ArpPacket<'a>, out: &mut [u8], pos: usize, Tracked(steps): Tracked<&mut Steps>) -> (r: Option<usize>) {
        self.wire.serialize(v, out, pos, Tracked(steps))
    }
}

} // verus!
