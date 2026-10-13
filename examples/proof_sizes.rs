//! Сколько строк занимают полные доказательства: `cargo run --example proof_sizes`.
use bourbaki_engine::logic::*;
use bourbaki_engine::*;

fn main() -> Result<()> {
    let th = Theory::build("L")
        .sign(&SpecialSign::relational("P", 0))
        .sign(&SpecialSign::relational("Q", 0))
        .sign(&SpecialSign::relational("R", 0))
        .logical()
        .done()?;
    let p = th.parse_rel("P")?;
    let q = th.parse_rel("Q")?;
    let r = th.parse_rel("R")?;
    let show = |name: &str, t: Theorem| {
        let d = t.demonstration();
        d.verify()
            .expect("доказательство должно проходить проверку");
        println!("{name:>8}: {:>6} строк   {}", d.len(), t.relation());
    };
    show("C8", c8(&th, &p)?);
    show("C12", c12(&th, &p, &q)?);
    show("C13", c13(&s2(&th, &p, &q)?, &r)?);
    show("C16", c16(&th, &p)?);
    show("C17", c17(&th, &p, &q)?);
    show("C21", and_left(&th, &p, &q)?);
    show("C20", and_intro(&c8(&th, &p)?, &c8(&th, &q)?)?);
    for src in [
        "¬¬P ⇔ P",
        "(P ⇒ Q) ⇔ (¬Q ⇒ ¬P)",
        "(P ⇒ Q) ⇒ ((Q ⇒ R) ⇒ (P ⇒ R))",
    ] {
        show("taut", taut(&th, &th.parse_rel(src)?)?);
    }
    Ok(())
}
