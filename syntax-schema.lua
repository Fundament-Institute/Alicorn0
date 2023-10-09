local schema = require "schema"

local S = schema.create(
	"alicorn0_syntax",
	"the raw format that an alicorn zero source text should be parsed into",
	"b2771894692e6ccdbb737b163d45ea90"
)

S:struct "anchor" "The source position information attached to a node" {
	schema.text "sourceid"(0) "the file name or other identifying information to locate and distinguish the original source of the code", --TODO: consider making this a generic parameter to accept structured data.
	schema.u32 "line"(1) "the line number in the file",
	schema.u32 "char"(2) "the offset within the line",
}

local element = S:addstruct("element")

element:define {
	S.export.anchor "anchor"(0) "the source location of the element",
	schema.union "kind"(1) "What syntactic element this represents" {
		schema.variant "list"(2) {
			schema.list(element) "elements"(3),
			S.export.anchor "endpos"(4),
		},
		schema.variant "symbol"(5) {
			schema.text "str"(6),
		},
		schema.variant "string"(7) {
			schema.list(element) "elements"(8) "A string contains a list of elements corresponding to parts of the literal. Every splice becomes a separate element, and the region between them is a literal byte buffer element",
			S.export.anchor "endpos"(9),
		},
		schema.variant "literal"(10) {
			schema.union "literaltype"(11) {
				schema.variant "u8"(12) {
					schema.u8 "val"(13),
				},
				schema.variant "i8"(14) {
					schema.i8 "val"(15),
				},
				schema.variant "u16"(16) {
					schema.u16 "val"(17),
				},
				schema.variant "i16"(18) {
					schema.i16 "val"(19),
				},
				schema.variant "u32"(20) {
					schema.u32 "val"(21),
				},
				schema.variant "i32"(22) {
					schema.i32 "val"(23),
				},
				schema.variant "u64"(24) {
					schema.u64 "val"(25),
				},
				schema.variant "i64"(26) {
					schema.i64 "val"(27),
				},
				schema.variant "f16"(28) {
					schema.f16 "val"(29),
				},
				schema.variant "f32"(30) {
					schema.f32 "val"(31),
				},
				schema.variant "f64"(32) {
					schema.f64 "val"(33),
				},
				schema.variant "bytes"(34) {
					schema.list(schema.u8) "val"(35),
				},
				schema.variant "unit"(36) {},
			},
		},
	},
}

return S
