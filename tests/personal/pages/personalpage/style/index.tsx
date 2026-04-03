import { StyleSheet } from 'react-native';
import { PublicFont, Theme, CommonUtils } from '@hw-vmall/vrn-basic-comp';

const SCALE_SIZE = 2;
export default (theme: Theme) =>
  StyleSheet.create({
    viewStyle: {
      backgroundColor: theme.C32.color,
    },
    lodingTitle: {
      fontSize: theme.T7.fontSize,
      color: theme.C13.color,
      opacity: theme.C13.opacity,
    },
    commonStyle: {
      backgroundColor: theme.S32.backgroundColor,
    },
    titleWrapper: {
      width: 1200,
      paddingVertical: 24,
      flexDirection: 'row',
      margin: 'auto',
      marginTop: 0,
      marginBottom: 0,
    },
    tabHome: {
      fontFamily: 'HarmonyHeiTi',
      ...theme.T3,
      ...theme.C12,
      fontWeight: '400',
    },
    dayu: {
      ...theme.T3,
      ...theme.C12,
      marginHorizontal: 2,
    },
    myshop: {
      fontFamily: PublicFont.fontFamilyMedium,
      ...theme.T4,
      ...theme.C11,
      fontWeight: '500',
    },
    onBack: {
      position: 'absolute',
      bottom: 48,
      right: 16,
      width: 50,
      height: 50,
    },
    boxNone: {
      position: 'absolute',
      top: 0,
      left: 0,
    },
    personalBody: {
      height: '100%',
      position: 'relative',
    },
    // 生日弹窗Modal
    birthModalLayer: {
      width: '100%',
      height: '100%',
      backgroundColor: 'rgba(0,0,0,0.38)',
      zIndex: 100,
      justifyContent: 'center',
      alignItems: 'center',
    },
    birthModalBox: {
      padding: 16,
      height: CommonUtils.getScaleSize(168, SCALE_SIZE),
      backgroundColor: 'rgba(255,255,255,1)',
      alignContent: 'center',
      borderRadius: 32,
      zIndex: 101,
      marginHorizontal: 16,
    },
    birthTitle: {
      textAlign: 'center',
      fontSize: CommonUtils.getScaleSize(theme.T12.fontSize, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(theme.T12.lineHeight, SCALE_SIZE),
      fontFamily: 'HarmonyHeiTi',
      fontWeight: '700',
    },
    birthSubTitle: {
      textAlign: 'center',
      marginTop: 15,
      lineHeight: CommonUtils.getScaleSize(theme.T9.lineHeight, SCALE_SIZE),
      fontSize: CommonUtils.getScaleSize(theme.T9.fontSize, SCALE_SIZE),
      fontFamily: 'HarmonyHeiTi',
      fontWeight: '500',
    },
    birthTips: {
      textAlign: 'center',
      marginTop: 8,
      fontSize: CommonUtils.getScaleSize(theme.T7.fontSize, SCALE_SIZE),
      lineHeight: CommonUtils.getScaleSize(theme.T7.lineHeight, SCALE_SIZE),
      fontFamily: 'HarmonyHeiTi',
      fontWeight: '400',
      color: '#000000',
      opacity: 0.6,
    },
    birthBtnContainer: {
      marginTop: 8,
      alignItems: 'center',
      display: 'flex',
      flexDirection: 'row',
    },
    birthBtn: {
      height: CommonUtils.getScaleSize(40, SCALE_SIZE),
      borderRadius: 20,
      alignItems: 'center',
      justifyContent: 'center',
    },
    receiveBtn: {
      backgroundColor: '#CE0E2D',
    },
    commonTxt: {
      fontWeight: '500',
      fontSize: CommonUtils.getScaleSize(theme.T10.fontSize, SCALE_SIZE),
    },
    giveUpTxt: {
      color: '#CF0A2C',
    },
    line: {
      width: 0.5,
      height: 24,
      backgroundColor: '#000000',
      opacity: 0.05,
    },
    receiveTxt: {
      color: '#FFFFFF',
    },
  });
