// HVM4 Metal Host Code
// =====================

import Foundation
import Metal

typealias Term = UInt64

// Tags
let NAM: UInt8 = 0, DRY: UInt8 = 1, REF: UInt8 = 2, ALO: UInt8 = 3, ERA: UInt8 = 4
let CO0: UInt8 = 5, CO1: UInt8 = 6, VAR: UInt8 = 7, LAM: UInt8 = 8, APP: UInt8 = 9
let SUP: UInt8 = 10, DUP: UInt8 = 11, MAT: UInt8 = 12, CTR: UInt8 = 13, CTR_MAX_ARI: UInt8 = 16

// Bit Layout
let SUB_SHIFT: UInt64 = 63, TAG_SHIFT: UInt64 = 56, EXT_SHIFT: UInt64 = 40
let TAG_MASK: UInt64 = 0x7F, EXT_MASK: UInt64 = 0xFFFF, VAL_MASK: UInt64 = 0xFFFFFFFFFF

// Capacities
let BOOK_CAP: Int = 1 << 24
let HEAP_PER_THR: UInt64 = 393216    // 3 MB in 8-byte slots
let WNF_PER_THR: UInt64 = 65536      // 512 KB in 8-byte entries
let SNF_PER_THR: UInt64 = 256        // 256 SNFFrame entries

// Globals for parsing
var HEAP: UnsafeMutablePointer<Term>!
var BOOK: UnsafeMutablePointer<UInt32>!
var ALLOC: UInt64 = 1

// Term Helpers
@inline(__always) func newTerm(_ sub: UInt8, _ tag: UInt8, _ ext: UInt32, _ val: UInt64) -> Term {
  (UInt64(sub) << SUB_SHIFT) | (UInt64(tag & UInt8(TAG_MASK)) << TAG_SHIFT)
  | (UInt64(ext & UInt32(EXT_MASK)) << EXT_SHIFT) | (val & VAL_MASK)
}
@inline(__always) func tag(_ t: Term) -> UInt8 { UInt8((t >> TAG_SHIFT) & TAG_MASK) }
@inline(__always) func ext(_ t: Term) -> UInt32 { UInt32((t >> EXT_SHIFT) & EXT_MASK) }
@inline(__always) func val(_ t: Term) -> UInt64 { t & VAL_MASK }
@inline(__always) func heapAlloc(_ size: UInt64) -> UInt64 { let at = ALLOC; ALLOC += size; return at }

// Names
let alphabet = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789$"

func charToB64(_ c: Character) -> Int {
  if c == "_" { return 0 }
  if c >= "a" && c <= "z" { return 1 + Int(c.asciiValue! - Character("a").asciiValue!) }
  if c >= "A" && c <= "Z" { return 27 + Int(c.asciiValue! - Character("A").asciiValue!) }
  if c >= "0" && c <= "9" { return 53 + Int(c.asciiValue! - Character("0").asciiValue!) }
  if c == "$" { return 63 }
  return -1
}

func isNameStart(_ c: Character) -> Bool { (c >= "a" && c <= "z") || (c >= "A" && c <= "Z") }
func isNameChar(_ c: Character) -> Bool { charToB64(c) >= 0 }

func nameToStr(_ n: UInt64) -> String {
  if n == 0 { return "_" }
  var result = "", val = n, chars: [Character] = []
  while val > 0 {
    chars.append(alphabet[alphabet.index(alphabet.startIndex, offsetBy: Int(val % 64))])
    val /= 64
  }
  for c in chars.reversed() { result.append(c) }
  return result
}

// Term Constructors
func Var(_ loc: UInt64) -> Term { newTerm(0, VAR, 0, loc) }
func Ref(_ nam: UInt32) -> Term { newTerm(0, REF, nam, 0) }
func Era() -> Term { newTerm(0, ERA, 0, 0) }

func Lam(_ bod: Term) -> Term {
  let loc = heapAlloc(1); HEAP[Int(loc)] = bod; return newTerm(0, LAM, 0, loc)
}
func App(_ fun: Term, _ arg: Term) -> Term {
  let loc = heapAlloc(2); HEAP[Int(loc)] = fun; HEAP[Int(loc) + 1] = arg; return newTerm(0, APP, 0, loc)
}
func Sup(_ lab: UInt32, _ tm0: Term, _ tm1: Term) -> Term {
  let loc = heapAlloc(2); HEAP[Int(loc)] = tm0; HEAP[Int(loc) + 1] = tm1; return newTerm(0, SUP, lab, loc)
}
func Dup(_ lab: UInt32, _ v: Term, _ bod: Term) -> Term {
  let loc = heapAlloc(2); HEAP[Int(loc)] = v; HEAP[Int(loc) + 1] = bod; return newTerm(0, DUP, lab, loc)
}
func Mat(_ nam: UInt32, _ v: Term, _ nxt: Term) -> Term {
  let loc = heapAlloc(2); HEAP[Int(loc)] = v; HEAP[Int(loc) + 1] = nxt; return newTerm(0, MAT, nam, loc)
}
func Ctr(_ nam: UInt32, _ args: [Term]) -> Term {
  let loc = heapAlloc(UInt64(args.count))
  for i in 0..<args.count { HEAP[Int(loc) + i] = args[i] }
  return newTerm(0, CTR + UInt8(args.count), nam, loc)
}

// Parser
struct PState { var file: String, src: String, pos: Int, line: Int, col: Int }
struct PBind { var name: UInt32, depth: UInt32, lab: UInt32 }
var PARSE_BINDS: [PBind] = []

func parseError(_ s: PState, _ expected: String, _ detected: Character?) {
  fputs("\u{001B}[1;31mPARSE_ERROR\u{001B}[0m (\(s.file):\(s.line):\(s.col))\n- expected: \(expected)\n", stderr)
  fputs(detected != nil ? "- detected: '\(detected!)'\n" : "- detected: EOF\n", stderr)
  exit(1)
}

func atEnd(_ s: PState) -> Bool { s.pos >= s.src.count }
func peek(_ s: PState) -> Character? { atEnd(s) ? nil : s.src[s.src.index(s.src.startIndex, offsetBy: s.pos)] }
func peekAt(_ s: PState, _ offset: Int) -> Character? {
  let idx = s.pos + offset; return idx >= s.src.count ? nil : s.src[s.src.index(s.src.startIndex, offsetBy: idx)]
}
func advance(_ s: inout PState) {
  if atEnd(s) { return }; if peek(s) == "\n" { s.line += 1; s.col = 1 } else { s.col += 1 }; s.pos += 1
}
func startsWith(_ s: PState, _ str: String) -> Bool {
  for (i, c) in str.enumerated() { if peekAt(s, i) != c { return false } }; return true
}
func match(_ s: inout PState, _ str: String) -> Bool {
  if !startsWith(s, str) { return false }; for _ in str { advance(&s) }; return true
}
func isSpace(_ c: Character) -> Bool { c == " " || c == "\t" || c == "\n" || c == "\r" }
func skip(_ s: inout PState) {
  while !atEnd(s) {
    if let c = peek(s), isSpace(c) { advance(&s); continue }
    if startsWith(s, "//") { while !atEnd(s) && peek(s) != "\n" { advance(&s) }; continue }
    break
  }
}
func consume(_ s: inout PState, _ str: String) { skip(&s); if !match(&s, str) { parseError(s, str, peek(s)) }; skip(&s) }
func bindPush(_ name: UInt32, _ depth: UInt32, _ lab: UInt32) { PARSE_BINDS.append(PBind(name: name, depth: depth, lab: lab)) }
func bindPop() { PARSE_BINDS.removeLast() }
func bindLookup(_ name: UInt32, _ depth: UInt32) -> (idx: Int, lab: UInt32) {
  for i in stride(from: PARSE_BINDS.count - 1, through: 0, by: -1) {
    if PARSE_BINDS[i].name == name { return (Int(depth) - 1 - Int(PARSE_BINDS[i].depth), PARSE_BINDS[i].lab) }
  }
  return (-1, 0)
}

func parseName(_ s: inout PState) -> UInt32 {
  skip(&s); guard let c = peek(s), isNameStart(c) else { parseError(s, "name", peek(s)); return 0 }
  var k: UInt32 = 0
  while let c = peek(s), isNameChar(c) { k = ((k << 6) + UInt32(charToB64(c))) & UInt32(EXT_MASK); advance(&s) }
  skip(&s); return k
}

func parseMatBody(_ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); if peek(s) == "}" { consume(&s, "}"); return Era() }
  if peek(s) == "#" {
    consume(&s, "#"); let nam = parseName(&s); consume(&s, ":")
    let v = parseTerm(&s, depth); skip(&s); _ = match(&s, ";"); skip(&s)
    return Mat(nam, v, parseMatBody(&s, depth))
  }
  let v = parseTerm(&s, depth); consume(&s, "}"); return v
}

func parseLam(_ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); if peek(s) == "{" { consume(&s, "{"); return parseMatBody(&s, depth) }
  let nam = parseName(&s); consume(&s, "."); bindPush(nam, depth, 0)
  let loc = heapAlloc(1); let body = parseTerm(&s, depth + 1)
  HEAP[Int(loc)] = body; bindPop(); return newTerm(0, LAM, depth, loc)
}

func parseDup(_ s: inout PState, _ depth: UInt32) -> Term {
  let nam = parseName(&s); consume(&s, "&"); let lab = parseName(&s); consume(&s, "=")
  let v = parseTerm(&s, depth); skip(&s); _ = match(&s, ";"); skip(&s); bindPush(nam, depth, lab)
  let loc = heapAlloc(2); HEAP[Int(loc)] = v
  let body = parseTerm(&s, depth + 1); HEAP[Int(loc) + 1] = body; bindPop()
  return newTerm(0, DUP, lab, loc)
}

func parseSup(_ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); if peek(s) == "{" { consume(&s, "{"); consume(&s, "}"); return Era() }
  let lab = parseName(&s); consume(&s, "{"); let tm0 = parseTerm(&s, depth)
  skip(&s); _ = match(&s, ","); skip(&s); let tm1 = parseTerm(&s, depth)
  consume(&s, "}"); return Sup(lab, tm0, tm1)
}

func parseCtr(_ s: inout PState, _ depth: UInt32) -> Term {
  let nam = parseName(&s); consume(&s, "{"); var args: [Term] = []; skip(&s)
  if peek(s) != "}" {
    while true { args.append(parseTerm(&s, depth)); skip(&s); if peek(s) == "," { consume(&s, ","); continue }; break }
  }
  consume(&s, "}"); return Ctr(nam, args)
}

func parseRef(_ s: inout PState) -> Term { Ref(parseName(&s)) }
func parsePar(_ s: inout PState, _ depth: UInt32) -> Term { let term = parseTerm(&s, depth); consume(&s, ")"); return term }

func parseVar(_ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); let nam = parseName(&s); let (idx, lab) = bindLookup(nam, depth); skip(&s)
  var side = -1; if match(&s, "₀") { side = 0 } else if match(&s, "₁") { side = 1 }; skip(&s)
  let v: UInt64 = idx >= 0 ? UInt64(idx) : UInt64(nam); let tg: UInt8 = side == 0 ? CO0 : (side == 1 ? CO1 : VAR)
  return newTerm(0, tg, lab, v)
}

func parseApp(_ f: Term, _ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); if peek(s) != "(" { return f }; var fun = f; consume(&s, "(")
  if peek(s) == ")" { consume(&s, ")"); return parseApp(fun, &s, depth) }
  while true {
    fun = App(fun, parseTerm(&s, depth)); skip(&s)
    if peek(s) == "," { consume(&s, ","); continue }
    if peek(s) == ")" { consume(&s, ")"); break }
    parseError(s, "',' or ')'", peek(s))
  }
  return parseApp(fun, &s, depth)
}

func parseTerm(_ s: inout PState, _ depth: UInt32) -> Term {
  skip(&s); var t: Term
  if match(&s, "λ") { t = parseLam(&s, depth) }
  else if match(&s, "!") { t = parseDup(&s, depth) }
  else if match(&s, "&") { t = parseSup(&s, depth) }
  else if match(&s, "#") { t = parseCtr(&s, depth) }
  else if match(&s, "@") { t = parseRef(&s) }
  else if match(&s, "(") { t = parsePar(&s, depth) }
  else { t = parseVar(&s, depth) }
  return parseApp(t, &s, depth)
}

func parseDef(_ s: inout PState) {
  skip(&s); if atEnd(s) { return }
  if match(&s, "@") {
    let nam = parseName(&s) & UInt32(EXT_MASK); consume(&s, "="); PARSE_BINDS = []
    let v = parseTerm(&s, 0); let loc = heapAlloc(1); HEAP[Int(loc)] = v; BOOK[Int(nam)] = UInt32(loc)
    parseDef(&s); return
  }
  parseError(s, "definition", peek(s))
}

// Result Stringifier
func strTerm(_ heap: UnsafePointer<Term>, _ term: Term, _ depth: UInt32 = 0) -> String {
  switch tag(term) {
    case VAR, NAM: return nameToStr(val(term))
    case REF: return "@\(nameToStr(UInt64(ext(term))))"
    case ERA: return "&{}"
    case CO0: return "\(nameToStr(val(term)))₀"
    case CO1: return "\(nameToStr(val(term)))₁"
    case LAM:
      let loc = val(term), nam = UInt64(depth + 1)
      return "λ\(nameToStr(nam)).\(strTerm(heap, heap[Int(loc)], depth + 1))"
    case APP, DRY:
      var spine: [Term] = [], curr = term
      while (tag(curr) == APP || tag(curr) == DRY) && spine.count < 256 {
        let loc = val(curr); spine.append(heap[Int(loc) + 1]); curr = heap[Int(loc)]
      }
      var result = tag(curr) == LAM ? "(\(strTerm(heap, curr, depth)))" : strTerm(heap, curr, depth)
      result += "("; for i in 0..<spine.count { if i > 0 { result += "," }; result += strTerm(heap, spine[spine.count - 1 - i], depth) }
      return result + ")"
    case SUP:
      let loc = val(term)
      return "&\(nameToStr(UInt64(ext(term)))){\(strTerm(heap, heap[Int(loc)], depth)),\(strTerm(heap, heap[Int(loc) + 1], depth))}"
    case DUP:
      let loc = val(term), nam = UInt64(depth + 1)
      return "!\(nameToStr(nam))&\(nameToStr(UInt64(ext(term))))=\(strTerm(heap, heap[Int(loc)], depth));\(strTerm(heap, heap[Int(loc) + 1], depth + 1))"
    case MAT:
      let loc = val(term)
      return "λ{#\(nameToStr(UInt64(ext(term)))):\(strTerm(heap, heap[Int(loc)], depth));\(strTerm(heap, heap[Int(loc) + 1], depth))}"
    case ALO: return "<ALO>"
    default:
      if tag(term) >= CTR && tag(term) <= CTR + CTR_MAX_ARI {
        let ari = Int(tag(term) - CTR), loc = val(term)
        var result = "#\(nameToStr(UInt64(ext(term)))){"
        for i in 0..<ari { if i > 0 { result += "," }; result += strTerm(heap, heap[Int(loc) + i], depth) }
        return result + "}"
      }
      return "<?>"
  }
}

// Metal Execution
func loadShaderSource() -> String? {
  let metalPath = URL(fileURLWithPath: CommandLine.arguments[0]).deletingLastPathComponent().appendingPathComponent("hvm4.metal")
  if let source = try? String(contentsOf: metalPath, encoding: .utf8) { return source }
  return try? String(contentsOfFile: "hvm4.metal", encoding: .utf8)
}

struct BenchResult { let time: Double, itrs: UInt64, mips: Double }

func runGPU(_ device: MTLDevice, _ shaderSource: String, _ bookSize: UInt32, _ mainName: UInt32, _ numThreads: Int) -> BenchResult {
  let library: MTLLibrary
  do { library = try device.makeLibrary(source: shaderSource, options: nil) }
  catch { fputs("Error compiling shader: \(error)\n", stderr); exit(1) }

  guard let function = library.makeFunction(name: "hvm_run") else { fputs("Error: kernel not found\n", stderr); exit(1) }
  let pipeline: MTLComputePipelineState
  do { pipeline = try device.makeComputePipelineState(function: function) }
  catch { fputs("Error creating pipeline: \(error)\n", stderr); exit(1) }
  guard let queue = device.makeCommandQueue() else { fputs("Error: no queue\n", stderr); exit(1) }

  let simdWidth = pipeline.threadExecutionWidth
  let numWarps = (numThreads + simdWidth - 1) / simdWidth
  let warpSliceSize = Int(HEAP_PER_THR) * simdWidth
  let totalHeapSize = Int(bookSize) + numWarps * warpSliceSize
  let totalWnfSize = numThreads * Int(WNF_PER_THR)
  let snfFrameSize = 24  // sizeof(SNFFrame): Term(8) + write_loc(4) + depth(4) + phase(1) + padding(7)
  let totalSnfSize = numThreads * Int(SNF_PER_THR) * snfFrameSize

  let heapBuffer = device.makeBuffer(length: totalHeapSize * MemoryLayout<Term>.stride, options: .storageModeShared)!
  memcpy(heapBuffer.contents(), HEAP, Int(bookSize) * MemoryLayout<Term>.stride)
  let wnfBuffer = device.makeBuffer(length: totalWnfSize * MemoryLayout<Term>.stride, options: .storageModeShared)!
  let snfBuffer = device.makeBuffer(length: totalSnfSize, options: .storageModeShared)!
  let bookBuffer = device.makeBuffer(bytes: BOOK, length: BOOK_CAP * MemoryLayout<UInt32>.stride, options: .storageModeShared)!
  let itrsBuffer = device.makeBuffer(length: numThreads * MemoryLayout<UInt64>.stride, options: .storageModeShared)!
  let outputsBuffer = device.makeBuffer(length: numThreads * MemoryLayout<Term>.stride, options: .storageModeShared)!

  var bookSizeVal = bookSize, mainRef = mainName, numThreadsVal = UInt32(numThreads)
  var heapPerThrVal = HEAP_PER_THR, wnfPerThrVal = WNF_PER_THR, snfPerThrVal = SNF_PER_THR, simdWidthVal = UInt32(simdWidth)
  let bookSizeBuffer = device.makeBuffer(bytes: &bookSizeVal, length: 4, options: .storageModeShared)!
  let mainRefBuffer = device.makeBuffer(bytes: &mainRef, length: 4, options: .storageModeShared)!
  let numThreadsBuffer = device.makeBuffer(bytes: &numThreadsVal, length: 4, options: .storageModeShared)!
  let heapPerThrBuffer = device.makeBuffer(bytes: &heapPerThrVal, length: 8, options: .storageModeShared)!
  let wnfPerThrBuffer = device.makeBuffer(bytes: &wnfPerThrVal, length: 8, options: .storageModeShared)!
  let snfPerThrBuffer = device.makeBuffer(bytes: &snfPerThrVal, length: 8, options: .storageModeShared)!
  let simdWidthBuffer = device.makeBuffer(bytes: &simdWidthVal, length: 4, options: .storageModeShared)!

  let threadsPerGroup = min(numThreads, 256)

  // Warm up
  for _ in 0..<3 {
    memcpy(heapBuffer.contents(), HEAP, Int(bookSize) * MemoryLayout<Term>.stride)
    guard let cmdBuffer = queue.makeCommandBuffer(), let encoder = cmdBuffer.makeComputeCommandEncoder() else { exit(1) }
    encoder.setComputePipelineState(pipeline)
    encoder.setBuffer(heapBuffer, offset: 0, index: 0)
    encoder.setBuffer(wnfBuffer, offset: 0, index: 1)
    encoder.setBuffer(snfBuffer, offset: 0, index: 2)
    encoder.setBuffer(bookBuffer, offset: 0, index: 3)
    encoder.setBuffer(itrsBuffer, offset: 0, index: 4)
    encoder.setBuffer(outputsBuffer, offset: 0, index: 5)
    encoder.setBuffer(bookSizeBuffer, offset: 0, index: 6)
    encoder.setBuffer(mainRefBuffer, offset: 0, index: 7)
    encoder.setBuffer(numThreadsBuffer, offset: 0, index: 8)
    encoder.setBuffer(heapPerThrBuffer, offset: 0, index: 9)
    encoder.setBuffer(wnfPerThrBuffer, offset: 0, index: 10)
    encoder.setBuffer(snfPerThrBuffer, offset: 0, index: 11)
    encoder.setBuffer(simdWidthBuffer, offset: 0, index: 12)
    encoder.dispatchThreads(MTLSize(width: numThreads, height: 1, depth: 1),
                            threadsPerThreadgroup: MTLSize(width: threadsPerGroup, height: 1, depth: 1))
    encoder.endEncoding(); cmdBuffer.commit(); cmdBuffer.waitUntilCompleted()
  }

  // Benchmark
  memcpy(heapBuffer.contents(), HEAP, Int(bookSize) * MemoryLayout<Term>.stride)
  guard let cmdBuffer = queue.makeCommandBuffer(), let encoder = cmdBuffer.makeComputeCommandEncoder() else { exit(1) }
  encoder.setComputePipelineState(pipeline)
  encoder.setBuffer(heapBuffer, offset: 0, index: 0)
  encoder.setBuffer(wnfBuffer, offset: 0, index: 1)
  encoder.setBuffer(snfBuffer, offset: 0, index: 2)
  encoder.setBuffer(bookBuffer, offset: 0, index: 3)
  encoder.setBuffer(itrsBuffer, offset: 0, index: 4)
  encoder.setBuffer(outputsBuffer, offset: 0, index: 5)
  encoder.setBuffer(bookSizeBuffer, offset: 0, index: 6)
  encoder.setBuffer(mainRefBuffer, offset: 0, index: 7)
  encoder.setBuffer(numThreadsBuffer, offset: 0, index: 8)
  encoder.setBuffer(heapPerThrBuffer, offset: 0, index: 9)
  encoder.setBuffer(wnfPerThrBuffer, offset: 0, index: 10)
  encoder.setBuffer(snfPerThrBuffer, offset: 0, index: 11)
  encoder.setBuffer(simdWidthBuffer, offset: 0, index: 12)
  encoder.dispatchThreads(MTLSize(width: numThreads, height: 1, depth: 1),
                          threadsPerThreadgroup: MTLSize(width: threadsPerGroup, height: 1, depth: 1))
  encoder.endEncoding()

  let start = DispatchTime.now()
  cmdBuffer.commit(); cmdBuffer.waitUntilCompleted()
  let end = DispatchTime.now()

  let wallTime = Double(end.uptimeNanoseconds - start.uptimeNanoseconds) / 1_000_000_000.0
  let itrsPtr = itrsBuffer.contents().bindMemory(to: UInt64.self, capacity: numThreads)
  var totalItrs: UInt64 = 0; for i in 0..<numThreads { totalItrs += itrsPtr[i] }
  let mips = Double(totalItrs) / wallTime / 1_000_000.0

  // Read packed stats from outputs buffer
  let outputsPtr = outputsBuffer.contents().bindMemory(to: UInt64.self, capacity: numThreads)
  let packed = outputsPtr[0]  // Just read thread 0's stats
  let wnfLoops = packed & 0xFFFFFFFF
  let snfLoops = (packed >> 32) & 0xFFFFFFFF
  if numThreads == 1 {
    print("  [Thread 0 stats] wnf_loop_iterations=\(wnfLoops), snf_loop_iterations=\(snfLoops)")
  }

  return BenchResult(time: wallTime, itrs: totalItrs, mips: mips)
}

func main() {
  guard let device = MTLCreateSystemDefaultDevice() else { fputs("Error: No Metal device\n", stderr); exit(1) }

  var numThreads = 1, srcPath: String? = nil, benchMode = false

  var i = 1
  while i < CommandLine.arguments.count {
    let arg = CommandLine.arguments[i]
    if arg.hasPrefix("-t"), let n = Int(arg.dropFirst(2)), n > 0 { numThreads = n }
    else if arg == "--bench" { benchMode = true }
    else { srcPath = arg }
    i += 1
  }

  let heapCap = 1 << 26
  HEAP = UnsafeMutablePointer<Term>.allocate(capacity: heapCap)
  HEAP.initialize(repeating: 0, count: heapCap)
  BOOK = UnsafeMutablePointer<UInt32>.allocate(capacity: BOOK_CAP)
  BOOK.initialize(repeating: 0, count: BOOK_CAP)

  let defaultSrc = """
    @ctru = λt.λf.t
    @cfal = λt.λf.f
    @cnot = λx.x(@cfal,@ctru)
    @P24  = λf.
      ! F &A = f;
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      ! F &A = λk. F₀(F₁(k));
      λk. F₀(F₁(k))
    @main = @P24(@cnot,@ctru)
    """

  var src = defaultSrc
  if let path = srcPath {
    if let contents = try? String(contentsOfFile: path, encoding: .utf8) { src = contents }
    else { fputs("Error: could not open '\(path)'\n", stderr); exit(1) }
  }

  var s = PState(file: srcPath ?? "<inline>", src: src, pos: 0, line: 1, col: 1)
  parseDef(&s)
  let bookSize = UInt32(ALLOC)

  var mainName: UInt32 = 0
  for c in "main" { mainName = ((mainName << 6) + UInt32(charToB64(c))) & UInt32(EXT_MASK) }
  guard BOOK[Int(mainName)] != 0 else { fputs("Error: @main not found\n", stderr); exit(1) }

  guard let shaderSource = loadShaderSource() else { fputs("Error: Could not load hvm4.metal\n", stderr); exit(1) }

/*  if benchMode {*/
    print("=== HVM4 Metal Benchmark ===")
    print("Device: \(device.name)")
    print("")
    print("Threads\tTime(s)\t\tIterations\tMIPS")
    print("-------\t-------\t\t----------\t----")
    for n in [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768] {
      let r = runGPU(device, shaderSource, bookSize, mainName, n)
      print("\(n)\t\(String(format: "%.6f", r.time))\t\(r.itrs)\t\t\(String(format: "%.2f", r.mips))")
    }
/*  } else {*/
/*    let r = runGPU(device, shaderSource, bookSize, mainName, numThreads)*/
/*    print("Threads: \(numThreads)")*/
/*    print("Iterations: \(r.itrs)")*/
/*    print("Time: \(String(format: "%.6f", r.time))s")*/
/*    print("Performance: \(String(format: "%.2f", r.mips)) MIPS")*/
/*  }*/
}

main()
