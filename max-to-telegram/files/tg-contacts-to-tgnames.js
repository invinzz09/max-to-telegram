// Выгрузка контактов Telegram Desktop (JSON) -> tgnames.json для пересыльщика MAX.
// Берёт ТОЛЬКО номер (последние 10 цифр) и подпись «Имя Фамилия», остальное отбрасывает.
// Запуск: node tg-contacts-to-tgnames.js <путь к result.json> [выход tgnames.json]
// Готовый файл положить в ВМ: C:\maxfwd\tgnames.json (пересыльщик перечитает сам, без перезапуска).
const fs = require('fs');
const src = process.argv[2], dst = process.argv[3] || 'tgnames.json';
if (!src) { console.error('укажи путь к result.json'); process.exit(1); }
// result.json (формат «JSON») или lists/contacts.html (формат «HTML») — оба понимает
const raw = fs.readFileSync(src, 'utf8');
let list;
if (/\.html?$/i.test(src)) {
  const unesc = s => s.replace(/<[^>]+>/g, '').replace(/&amp;/g, '&').replace(/&lt;/g, '<').replace(/&gt;/g, '>')
    .replace(/&quot;/g, '"').replace(/&#39;|&apos;/g, "'").replace(/\s+/g, ' ').trim();
  list = raw.split('<div class="entry clearfix">').slice(1).map(e => {
    const nm = (e.match(/<div class="name bold">([\s\S]*?)<\/div>/) || [])[1] || '';
    const ph = (e.match(/<div class="details_entry details">([\s\S]*?)<\/div>/) || [])[1] || '';
    return { first_name: unesc(nm), last_name: '', phone_number: unesc(ph) };
  });
} else {
  const j = JSON.parse(raw);
  list = (j.contacts && j.contacts.list) || j.list || [];
}
const out = {}; let skipped = 0, dup = 0;
for (const c of list) {
  const digits = String(c.phone_number || '').replace(/\D/g, '').slice(-10);
  const name = [c.first_name, c.last_name].map(s => (s || '').trim()).filter(Boolean).join(' ');
  if (digits.length < 10 || !name) { skipped++; continue; }
  if (out[digits]) { dup++; continue; }
  out[digits] = name;
}
fs.writeFileSync(dst, JSON.stringify(out, null, 1), 'utf8');
console.log(`контактов: ${list.length}, записано: ${Object.keys(out).length}, без номера/имени: ${skipped}, дублей номера: ${dup} -> ${dst}`);
