import {app, BrowserWindow} from 'electron'

let win : BrowserWindow | null = null

app.on('ready', () => {
    win = new BrowserWindow({width: 1920, height: 1200})
    win.loadURL('file://' + __dirname + '/index.html')
    //win.webContents.openDevTools()
    win.on('close', () => {
        win = null
    })
})